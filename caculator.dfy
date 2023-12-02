class Calculator {
    var expression: string;
    var numList: seq<int>;
    var opList: seq<char>;

    constructor(expr: string)
        modifies this
        requires expr != null && IsValidExpression(expr)
        ensures ValidCalculatorState()
    {
        expression := expr;
        (numList, opList) := ParseExpression(expression);
    }

    method ParseExpression(expr: string) returns (nums: seq<int>, ops: seq<char>)
        requires expr != null && IsValidExpression(expr)
        ensures nums.Length == ops.Length + 1
    {
        //
        
    }

    method Evaluate() returns (result: int)
        requires ValidCalculatorState()
        ensures result == EvaluateExpression(numList, opList)
    {
        var nums := numList;
        var ops := opList;
        var i := 0;

        while i < ops.Length
            invariant 0 <= i <= ops.Length
            invariant nums.Length == ops.Length + 1 - i
        {
            if ops[i] == '+' {
                nums[i] := nums[i] + nums[i+1];
                nums := nums[0..i] + nums[i+2..];
                ops := ops[0..i] + ops[i+1..];
            } else if ops[i] == '-' {
                nums[i] := nums[i] - nums[i+1];
                nums := nums[0..i] + nums[i+2..];
                ops := ops[0..i] + ops[i+1..];
            }
            i := i + 1;
        }

        return nums[0];
    }


}

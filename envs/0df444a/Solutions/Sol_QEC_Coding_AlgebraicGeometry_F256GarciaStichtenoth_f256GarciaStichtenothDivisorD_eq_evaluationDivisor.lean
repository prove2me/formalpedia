-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorD_eq_evaluationDivisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:38:24.616306+00:00
-- url     : https://prove2.me/submissions/097d802f-34e4-4067-a60d-84c371510e8b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    f256GarciaStichtenothDivisorD i =
      evaluationDivisor (f256GarciaStichtenothSelectedRationalPlace i) := rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

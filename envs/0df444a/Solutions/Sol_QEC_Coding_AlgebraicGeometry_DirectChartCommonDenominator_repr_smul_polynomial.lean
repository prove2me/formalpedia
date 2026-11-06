-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.repr_smul_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:04:19.370931+00:00
-- url     : https://prove2.me/submissions/60ea177c-b880-4fc4-996e-aa12ce3b31e5

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
open scoped BigOperators Polynomial
variable {k F ι : Type*}
variable [Field k] [Field F]
variable [Algebra (RatFunc k) F] [Algebra (Polynomial k) F]
  [IsScalarTower (Polynomial k) (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
theorem _root_.solution (b : Module.Basis ι (RatFunc k) F) (a : Polynomial k) (x : F) (j : ι) :
    b.repr (a • x) j = algebraMap (Polynomial k) (RatFunc k) a * b.repr x j := by
  simpa [Finsupp.smul_apply, Algebra.smul_def] using
    congrArg (fun c : ι →₀ RatFunc k => c j)
      ((b.repr.restrictScalars (Polynomial k)).map_smul a x)
end QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator

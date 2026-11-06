-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_add_coefficient_nonnegative_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:25:45.752524+00:00
-- url     : https://prove2.me/submissions/15d9db2d-ea59-4214-8d8f-f104da83eb7f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) {f : F}
    (hmem : f ∈ GlobalPlace.riemannRochSubmodule G) (hf : f ≠ 0)
    (P : GlobalPlace k F) :
    0 ≤ GlobalPlace.order P f + G P := by
  have hbound : P.valuation f ≤ WithZero.exp (G P) :=
    (GlobalPlace.mem_riemannRochSubmodule_iff G f).mp hmem P
  have hlog : WithZero.log (P.valuation f) ≤ G P :=
    (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf)).mpr hbound
  change 0 ≤ -WithZero.log (P.valuation f) + G P
  omega
end GlobalPlace
end QEC.Coding.AlgebraicGeometry

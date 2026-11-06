-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_weighted_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:36.98606+00:00
-- url     : https://prove2.me/submissions/8d915e1a-936c-44ee-8b87-78e2fdb6adb2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution (f : Fˣ) :
    (GlobalPlace.principalDivisor (k := k) (F := F) f).sum
        (fun P coefficient => coefficient *
          (GlobalPlace.residueDegree (k := k) (F := F) P : Int)) = 0 :=
  GlobalPlace.principalDivisor_degree_zero k F f
end GlobalPlace
end QEC.Coding.AlgebraicGeometry

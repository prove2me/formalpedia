-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:25.638611+00:00
-- url     : https://prove2.me/submissions/be38b64f-3945-45e8-a36c-8a03bf56f885

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectPrincipalDegree_direct_chart_degree_eq_fieldNorm_intDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_eq_chartContributions
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibrePrincipalDegree_inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_add_normalizedDegree

section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]
private theorem fieldNorm_ne_zero (f : Fˣ) :
    Algebra.norm k⟮X⟯ (f : F) ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr f.ne_zero
end QEC.Coding.AlgebraicGeometry
end

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
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
      (GlobalPlace.principalDivisor (k := k) (F := F) f) = 0 := by
  rw [GlobalPlace.principalDivisor_degree_eq_chartContributions,
    DirectPrincipalDegree.direct_chart_degree_eq_fieldNorm_intDegree,
    _root_.QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order]
  rw [add_comm]
  exact
    RationalBaseInfinityCancellation.rationalInfinity_order_add_normalizedDegree k
      (Algebra.norm k⟮X⟯ (f : F)) (fieldNorm_ne_zero k F f)
end GlobalPlace
end QEC.Coding.AlgebraicGeometry

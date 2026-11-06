-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.divisorDegree_nonnegative_of_mem_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:40.957286+00:00
-- url     : https://prove2.me/submissions/42c0ee0d-5c51-4e19-9865-cdb63cad0f21

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_add_coefficient_nonnegative_of_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation



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
    (hmem : f ∈ GlobalPlace.riemannRochSubmodule G) (hf : f ≠ 0) :
    0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G := by
  let u : Fˣ := Units.mk0 f hf
  have hpositive : Divisor.Nonnegative
      (GlobalPlace.principalDivisor (k := k) (F := F) u + G) := by
    intro P
    rw [Finsupp.add_apply, GlobalPlace.principalDivisor_apply]
    exact
      (GlobalPlace.order_add_coefficient_nonnegative_of_mem k F G hmem hf P)
  have hdegree :
      0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) :=
    Divisor.degree_nonnegative (GlobalPlace.residueDegree (k := k) (F := F))
      (GlobalPlace.principalDivisor (k := k) (F := F) u + G) hpositive
  rw [Divisor.degree_add, GlobalPlace.principalDivisor_degree_zero] at hdegree
  simpa using hdegree
end GlobalPlace
end QEC.Coding.AlgebraicGeometry

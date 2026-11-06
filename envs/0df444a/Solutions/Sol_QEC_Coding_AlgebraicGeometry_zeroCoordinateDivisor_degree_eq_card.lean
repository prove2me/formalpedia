-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_degree_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:23:23.439977+00:00
-- url     : https://prove2.me/submissions/94bf35c2-5423-4719-8714-59401ba5609a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_globalResidueDegree_eq_one
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
private theorem divisor_degree_single (degreeOf : GlobalPlace k F → ℕ)
    (P : GlobalPlace k F) (coefficient : ℤ) :
    Divisor.degree degreeOf (Finsupp.single P coefficient) =
      coefficient * (degreeOf P : ℤ) := by
  simp [Divisor.degree, Divisor.degreeHom]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : ι → RationalPlace k F) (S : Finset ι) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (zeroCoordinateDivisor Q S) = S.card := by
  classical
  unfold zeroCoordinateDivisor
  change Divisor.degreeHom (GlobalPlace.residueDegree (k := k) (F := F))
      (∑ i ∈ S, Finsupp.single (Q i).place (1 : ℤ)) = S.card
  rw [map_sum]
  calc
    (∑ i ∈ S, Divisor.degreeHom (GlobalPlace.residueDegree (k := k) (F := F))
        (Finsupp.single (Q i).place (1 : ℤ))) =
        ∑ i ∈ S, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      change Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (Finsupp.single (Q i).place (1 : ℤ)) = (1 : ℤ)
      rw [divisor_degree_single,
        RationalPlace.globalResidueDegree_eq_one]
      simp
    _ = S.card := by simp
end QEC.Coding.AlgebraicGeometry

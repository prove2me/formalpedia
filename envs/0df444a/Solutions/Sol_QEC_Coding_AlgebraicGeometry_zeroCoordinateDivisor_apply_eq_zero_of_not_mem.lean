-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:22:43.070878+00:00
-- url     : https://prove2.me/submissions/f18181a0-d475-4b11-99ae-8945d080f66a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (Q : ι → RationalPlace k F)
    (S : Finset ι) (P : GlobalPlace k F)
    (hP : ∀ i ∈ S, (Q i).place ≠ P) :
    zeroCoordinateDivisor Q S P = 0 := by
  classical
  unfold zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp [Finsupp.single_apply, hP i hi]
end QEC.Coding.AlgebraicGeometry

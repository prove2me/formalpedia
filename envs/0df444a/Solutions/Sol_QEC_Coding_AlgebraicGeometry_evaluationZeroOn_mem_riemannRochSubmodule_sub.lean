-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.evaluationZeroOn_mem_riemannRochSubmodule_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:25:10.638195+00:00
-- url     : https://prove2.me/submissions/f8cb8123-1e6c-47d6-9c90-2df3388534fa

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_at
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
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


attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hzero : ∀ i, i ∈ S → agEvaluationLinearMap G Q hG f i = 0) :
    (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) := by
  rw [GlobalPlace.mem_riemannRochSubmodule_iff]
  intro P
  classical
  by_cases hP : ∃ i, i ∈ S ∧ (Q i).place = P
  · obtain ⟨i, hi, rfl⟩ := hP
    have hcoordinate :
        (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i) = 0 := by
      simpa only [agEvaluationLinearMap_apply] using hzero i hi
    have hmaximal :
        (⟨(f : F), (GlobalPlace.mem_valuationRing_iff (Q i).place (f : F)).mpr
          (evaluationRegularity G Q hG f i)⟩ : GlobalPlace.valuationRing (Q i).place) ∈
          IsLocalRing.maximalIdeal (GlobalPlace.valuationRing (Q i).place) :=
      (Q i).evaluateRegular_eq_zero_iff (f : F)
        (evaluationRegularity G Q hG f i) |>.mp hcoordinate
    rw [Valuation.mem_maximalIdeal_iff] at hmaximal
    change (Q i).place.valuation (f : F) < 1 at hmaximal
    rw [Finsupp.sub_apply, hG i, zeroCoordinateDivisor_apply_at Q hQ S hi]
    by_cases hf : (f : F) = 0
    · simp [hf]
    · have hvaluation_ne_zero : (Q i).place.valuation (f : F) ≠ 0 :=
        ((Q i).place.valuation.ne_zero_iff).mpr hf
      have hlog_lt : WithZero.log ((Q i).place.valuation (f : F)) < 0 := by
        rw [← WithZero.exp_log hvaluation_ne_zero, ← WithZero.exp_zero] at hmaximal
        exact WithZero.exp_lt_exp.mp hmaximal
      have hlog_le : WithZero.log ((Q i).place.valuation (f : F)) ≤ (-1 : ℤ) := by
        omega
      exact (WithZero.log_le_iff_le_exp hvaluation_ne_zero).mp hlog_le
  · have hdivisor_zero : zeroCoordinateDivisor Q S P = 0 :=
      zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q S P (by
        intro i hi hplace
        exact hP ⟨i, hi, hplace⟩)
    rw [Finsupp.sub_apply, hdivisor_zero, sub_zero]
    exact (GlobalPlace.mem_riemannRochSubmodule_iff G (f : F)).mp f.property P
end QEC.Coding.AlgebraicGeometry

-- Prove2me | solution 1 for ProbabilityTheory.measureEntropy_le_card_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:00.573287+00:00
-- url     : https://prove2.me/submissions/4c3c195d-3381-40a1-b7db-df0f3ec1b506

module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal NNReal Topology
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]
variable {μ : Measure S}
variable [MeasurableSingletonClass S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution {μ : Measure S} [IsProbabilityMeasure μ]
    (A : Finset S) (hμ : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have μA : μ A = 1 := by
    rw [← compl_compl (A : Set S), measure_compl A.measurableSet.compl (measure_ne_top _ _), hμ]
    simp
  let N := A.card
  have N_pos : (0 : ℝ) < N := by
    rcases Finset.eq_empty_or_nonempty A with rfl|hA
    · simp at μA
    · simpa [N] using Finset.card_pos.mpr hA
  simp only [measureEntropy, measure_univ, inv_one, one_smul]
  calc
  ∑' x, negMulLog (μ.real {x})
    = ∑ x ∈ A, negMulLog (μ.real {x}) := by
      apply tsum_eq_sum
      intro i hi
      have : μ {i} = 0 :=
        le_antisymm ((measure_mono (by simpa using hi)).trans (le_of_eq hμ)) bot_le
      simp [Measure.real, this]
  _ = N * ∑ x ∈ A, (N : ℝ)⁻¹ * negMulLog (μ.real {x}) := by
      rw [Finset.mul_sum]
      congr with x
      rw [← mul_assoc, mul_inv_cancel₀, one_mul]
      exact N_pos.ne'
  _ ≤ N * negMulLog (∑ x ∈ A, (N : ℝ)⁻¹ * (μ.real {x})) := by
      gcongr
      exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [mul_inv_cancel₀ N_pos.ne', N])
        (by simp)
  _ = N * negMulLog ((N : ℝ)⁻¹) := by simp [← Finset.mul_sum]; simp [μA, Measure.real]
  _ = log A.card := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ N_pos.ne', N]
end _root_.ProbabilityTheory
end ProbabilityTheory

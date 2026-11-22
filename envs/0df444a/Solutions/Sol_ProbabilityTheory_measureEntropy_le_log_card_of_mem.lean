-- Prove2me | solution 1 for ProbabilityTheory.measureEntropy_le_log_card_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:48.027411+00:00
-- url     : https://prove2.me/submissions/96509f22-1b2c-409d-a903-4a0a531cd111

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
public import Theorems.Thm_ProbabilityTheory_measureEntropy_le_card_aux
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
theorem _root_.solution
    {A : Finset S} (μ : Measure S) (hμA : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have h_log_card_nonneg : 0 ≤ log (Nat.card A) := log_natCast_nonneg (Nat.card ↑A)
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simpa only [measureEntropy_zero] using (log_natCast_nonneg A.card)
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureEntropy_univ_smul]
    exact measureEntropy_le_card_aux A <| by simp [hμA]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    exact log_natCast_nonneg _
end _root_.ProbabilityTheory
end ProbabilityTheory

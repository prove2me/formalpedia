-- Prove2me | solution 1 for ProbabilityTheory.entropy_of_uniformOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:26.127144+00:00
-- url     : https://prove2.me/submissions/3a719a22-1ea7-44e4-beb6-4e48450d4cd5

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
public import Theorems.Thm_ProbabilityTheory_uniformOn_real
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
theorem _root_.solution (H : Set S) [Nonempty H] [Finite H] :
    measureEntropy (uniformOn H) = log (Nat.card H) := by
  simp only [measureEntropy, measure_univ, inv_one, one_smul, Set.toFinite, uniformOn_real]
  classical
  calc ∑' s, negMulLog ((Nat.card (H ∩ {s} : Set S)) / Nat.card H)
    _ = ∑' s, if s ∈ H then negMulLog (1 / Nat.card H) else 0 := by
      congr with s; by_cases h : s ∈ H <;> simp [h]
    _ = ∑ s ∈ H.toFinite.toFinset, negMulLog (1 / Nat.card H) := by
      convert tsum_eq_sum (s := H.toFinite.toFinset) ?_ using 2 with s hs
      · simp at hs; simp [hs]
      · constructor
        simp
      simp_all
    _ = (Nat.card H) * negMulLog (1 / Nat.card H) := by simp [← Set.ncard_coe_finset]
    _ = log (Nat.card H) := by
      simp only [negMulLog, one_div, log_inv, mul_neg, neg_mul, neg_neg, ← mul_assoc]
      rw [mul_inv_cancel₀, one_mul]
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨‹_›, ‹_›⟩
end _root_.ProbabilityTheory
end ProbabilityTheory

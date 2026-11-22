-- Prove2me | solution 1 for ProbabilityTheory.measureEntropy_eq_card_iff_measureReal_eq_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:47.729038+00:00
-- url     : https://prove2.me/submissions/6ee6854e-b637-4f3b-841c-8acb4276fa3d

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
theorem _root_.solution [Fintype S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s, μ.real {s} = (Fintype.card S : ℝ)⁻¹ := by
  cases isEmpty_or_nonempty S
  · simp [Fintype.card_eq_zero, Subsingleton.elim μ 0]
  -- multiply LHS equation through by `N⁻¹`
  set N := Fintype.card S
  have hN : (N:ℝ)⁻¹ ≠ 0 := by positivity
  rw [← mul_right_inj' hN]
  -- setup to use equality case of Jensen
  let w (_ : S) := (N:ℝ)⁻¹
  have hw1 : ∀ s ∈ Finset.univ, 0 < w s := by intros; positivity
  have hw2 : ∑ s : S, w s = 1 := by simp [w, Finset.card_univ, N]
  let p (s : S) := μ.real {s}
  have hp : ∀ s ∈ Finset.univ, 0 ≤ p s := by intros; positivity
  rw [measureEntropy, tsum_fintype, eq_comm]
  convert strictConcaveOn_negMulLog.map_sum_eq_iff hw1 hw2 hp using 2
  · simp [w, p, negMulLog, ← Finset.mul_sum]
  · simp [Finset.mul_sum, w, p]
  · simp [p, ← Finset.mul_sum, w, p]
end _root_.ProbabilityTheory
end ProbabilityTheory

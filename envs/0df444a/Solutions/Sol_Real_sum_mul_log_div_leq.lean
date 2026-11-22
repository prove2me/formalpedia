-- Prove2me | solution 1 for Real.sum_mul_log_div_leq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:16.427886+00:00
-- url     : https://prove2.me/submissions/09fc1bc6-93e9-40eb-ad28-eac7817d2c93

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal Topology
open Real
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {p : ι → ℝ}
namespace Real
theorem _root_.solution {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s,
  0 ≤ b i)
    (habs : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s,
      a i * log (a i / b i) := by
  by_cases h : ∀ i ∈ s, b i = 0
  · simp_all
  let B := ∑ i ∈ s, b i
  have B_pos : 0 < B := by
    apply Finset.sum_pos' hb
    simp only [not_forall] at h
    rcases h with ⟨i, hi, h'i⟩
    exact ⟨i, hi, lt_of_le_of_ne (hb i hi) (Ne.symm h'i)⟩
  suffices - (∑ i ∈ s, a i * log (a i / b i)) / B ≤
        - ((∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) / B by
    rwa [div_le_div_iff_of_pos_right B_pos, neg_le_neg_iff] at this
  have A : ∑ i ∈ s, b i / B = 1 := by simp [← Finset.sum_div, B, div_self B_pos.ne']
  have A' : ∀ i ∈ s, 0 ≤ b i / B := fun i hi ↦ div_nonneg (hb i hi) B_pos.le
  have A'' : ∀ i ∈ s, 0 ≤ a i / b i := fun i hi ↦ div_nonneg (ha i hi) (hb i hi)
  have hLHS : - (∑ i ∈ s, a i * log (a i / b i)) / B =
      ∑ i ∈ s, (b i / B) • (Real.negMulLog (a i / b i)) := by
    simp only [negMulLog, smul_eq_mul, neg_mul, mul_neg, Finset.sum_neg_distrib]
    rw [neg_div, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    rcases eq_or_lt_of_le (hb i hi) with h'i | h'i
    · simp [← h'i, habs i hi h'i.symm]
    · field_simp
  have hsum : ∑ i ∈ s, (b i / B) • (a i / b i) = (∑ i ∈ s, a i) / B := by
    simp only [smul_eq_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    rcases eq_or_lt_of_le (hb i hi) with h'i | h'i
    · simp [← h'i, habs i hi h'i.symm]
    · field_simp
  have hRHS : - ((∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) / B =
      Real.negMulLog (∑ i ∈ s, (b i / B) • (a i / b i)) := by
    rw [hsum]
    simp only [negMulLog, neg_mul, B]
    ring
  rw [hLHS, hRHS]
  exact ConcaveOn.le_map_sum Real.concaveOn_negMulLog A' A (p := fun i ↦ a i / b i) A''
end Real

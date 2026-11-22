-- Prove2me | solution 1 for Real.sum_mul_log_div_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:49.859508+00:00
-- url     : https://prove2.me/submissions/4916489b-d21f-4772-b158-cb08afa2ff65

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog
public import Theorems.Thm_Real_sum_mul_log_div_eq_iff_aux

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal Topology
open Real
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {p : ι → ℝ}
namespace Real
theorem _root_.solution {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s,
  0 ≤ b i)
    (habs : ∀ i ∈ s, b i = 0 → a i = 0)
    (heq : ∑ i ∈ s, a i * log (a i / b i)
      = (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) :
    ∃ r, ∀ i ∈ s, a i = r * (b i) := by
  let s' : Finset ι := s.filter (fun i ↦ 0 < b i)
  have A : ∑ i ∈ s', a i = ∑ i ∈ s, a i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi h'i
    simp only [Finset.mem_filter, hi, true_and, not_lt] at h'i
    exact habs i hi (le_antisymm h'i (hb i hi))
  have B : ∑ i ∈ s', b i = ∑ i ∈ s, b i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi h'i
    simp only [Finset.mem_filter, hi, true_and, not_lt] at h'i
    exact le_antisymm h'i (hb i hi)
  have C : ∑ i ∈ s', a i * log (a i / b i) =
      (∑ i ∈ s', a i) * log ((∑ i ∈ s', a i) / (∑ i ∈ s', b i)) := by
    convert heq using 1
    · apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi h'i
      simp only [Finset.mem_filter, hi, true_and, not_lt] at h'i
      have : b i = 0 := le_antisymm h'i (hb i hi)
      simp [this]
    · simp [A, B]
  obtain ⟨r, hr⟩ : ∃ r, ∀ i ∈ s', a i = r * (b i) := by
    apply sum_mul_log_div_eq_iff_aux (fun i hi ↦ ha i ?_) (fun i hi ↦ ?_) C
    · simp only [Finset.mem_filter, s'] at hi
      exact hi.1
    · simp only [Finset.mem_filter, s'] at hi
      exact hi.2
  refine ⟨r, fun i hi ↦ ?_⟩
  rcases eq_or_lt_of_le (hb i hi) with h'i | h'i
  · simp [← h'i, habs i hi h'i.symm]
  · apply hr
    simp [s', hi, h'i]
end Real

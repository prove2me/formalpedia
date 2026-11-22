-- Prove2me | solution 1 for Real.sum_mul_log_div_eq_iff_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:16.963501+00:00
-- url     : https://prove2.me/submissions/22a98368-eb98-4b20-9906-bf8273dfebb0

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
theorem _root_.solution {a b : ι → ℝ} (ha : ∀ i ∈ s,
  0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (heq : ∑ i ∈ s, a i * log (a i / b i) = (∑ i ∈ s, a i) * log ((∑ i ∈ s,
      a i) / ∑ i ∈ s, b i)) :
    ∃ r, ∀ i ∈ s, a i = r * (b i) := by
  rcases Finset.eq_empty_or_nonempty s with rfl | h's
  · simp
  let B := ∑ i ∈ s, b i
  have B_pos : 0 < B := Finset.sum_pos hb h's
  suffices ∀ j ∈ s, a j / b j = ∑ i ∈ s, (b i / B) * (a i / b i) by
    refine ⟨∑ i ∈ s, (b i / B) * (a i / b i), fun j hj ↦ ?_⟩
    specialize this j hj
    rwa [div_eq_iff (hb j hj).ne'] at this
  have A : ∑ i ∈ s, b i / B = 1 := by simp [← Finset.sum_div, B, div_self B_pos.ne']
  have A' : ∀ i ∈ s, 0 < b i / B := fun i hi ↦ div_pos (hb i hi) B_pos
  have A'' : ∀ i ∈ s, 0 ≤ a i / b i := fun i hi ↦ div_nonneg (ha i hi) (hb i hi).le
  apply (StrictConcaveOn.map_sum_eq_iff Real.strictConcaveOn_negMulLog A' A A'').1
  have : ∑ x ∈ s, b x / B * (a x / b x) = (∑ x ∈ s, a x) / B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    have : 0 < b i := hb i hi
    field_simp
  simp only [negMulLog, smul_eq_mul, this, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [← mul_div_right_comm, ← heq, Finset.sum_div]
  apply Finset.sum_congr rfl (fun i hi ↦ ?_)
  have : 0 < b i := hb i hi
  field_simp
end Real

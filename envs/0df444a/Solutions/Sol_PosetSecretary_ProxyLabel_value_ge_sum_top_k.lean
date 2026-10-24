-- Prove2me | solution 1 for PosetSecretary.ProxyLabel.value_ge_sum_top_k
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:18:29.604863+00:00
-- url     : https://prove2.me/submissions/46020d0c-a8b1-4c73-ad7c-700f55dcf50d

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

open PosetSecretary.ProxyLabel

theorem solution {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw0 : ∀ a, 0 ≤ w a) (k ω' : ℕ) :
    ∑ a ∈ Finset.univ.filter (fun a => (Finset.univ.filter (fun b => w a < w b)).card < k),
        selectionProb k ω' a * w a ≤ proxyLabelValue w k ω' := by
  classical
  set T := Finset.univ.filter (fun a => (Finset.univ.filter (fun b => w a < w b)).card < k)
  set N := Fintype.card α
  have hp0 : 0 ≤ sampleProb ω' := by unfold sampleProb; positivity
  have hp1 : sampleProb ω' ≤ 1 := by
    unfold sampleProb; rw [div_le_one (by positivity)]; linarith
  have hW : ∀ m, 0 ≤ (1 / (N.factorial : ℝ)) * (1 / (k : ℝ) ^ N) *
      binomWeight N m (sampleProb ω') := by
    intro m; unfold binomWeight
    have : 0 ≤ 1 - sampleProb ω' := by linarith
    positivity
  unfold selectionProb proxyLabelValue
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun pos _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun m _ => ?_
  set W := (1 / (N.factorial : ℝ)) * (1 / (k : ℝ) ^ N) * binomWeight N m (sampleProb ω')
  rw [Finset.mul_sum]
  have h1 : ∑ a ∈ T, W * (if a ∈ selected pos ℓ m then 1 else 0) * w a
      = ∑ a ∈ T ∩ selected pos ℓ m, W * w a := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun a => a ∈ selected pos ℓ m)]
    rw [Finset.sum_eq_zero (s := T.filter (fun a => a ∉ selected pos ℓ m)) (by
      intro a ha; simp at ha; simp [ha.2])]
    rw [add_zero, Finset.filter_mem_eq_inter]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp at ha; simp [ha.2]
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun a _ _ => mul_nonneg (hW m) (hw0 a))

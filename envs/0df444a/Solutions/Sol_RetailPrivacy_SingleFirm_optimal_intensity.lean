-- Prove2me | solution 1 for RetailPrivacy.SingleFirm.optimal_intensity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:33:54.859099+00:00
-- url     : https://prove2.me/submissions/6161cb13-75b3-42a9-9159-fcb104c3c5d5

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

set_option autoImplicit false
open RetailPrivacy.SingleFirm

theorem solution (c δ s : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs : 0 ≤ s) :
    IsMaxOn (fun r => dataProfit c δ s r) (Set.Ici 0) (δ * s / (2 * c)) ∧
    (∀ r ∈ Set.Ici (0 : ℝ), IsMaxOn (fun r' => dataProfit c δ s r') (Set.Ici 0) r →
      r = δ * s / (2 * c)) ∧
    StrictMono (fun s' : ℝ => δ * s' / (2 * c)) := by
  have key : ∀ r : ℝ, dataProfit c δ s r = c * (δ * s / (2 * c)) ^ 2 - c * (r - δ * s / (2 * c)) ^ 2 := by
    intro r
    unfold dataProfit
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro r _
    show dataProfit c δ s r ≤ dataProfit c δ s (δ * s / (2 * c))
    rw [key r, key (δ * s / (2 * c))]
    have : 0 ≤ c * (r - δ * s / (2 * c)) ^ 2 := by positivity
    nlinarith
  · intro r hr hmax
    have hle : dataProfit c δ s (δ * s / (2 * c)) ≤ dataProfit c δ s r :=
      hmax (show δ * s / (2 * c) ∈ Set.Ici (0:ℝ) from by
        simp only [Set.mem_Ici]; positivity)
    rw [key r, key (δ * s / (2 * c))] at hle
    have h2 : c * (r - δ * s / (2 * c)) ^ 2 ≤ 0 := by nlinarith
    have h3 : (r - δ * s / (2 * c)) ^ 2 ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos hc hcon]
    have : r - δ * s / (2 * c) = 0 := by nlinarith [sq_nonneg (r - δ * s / (2 * c))]
    linarith
  · intro a b hab
    simp only
    have : 0 < 2 * c := by positivity
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hab hδ0) this

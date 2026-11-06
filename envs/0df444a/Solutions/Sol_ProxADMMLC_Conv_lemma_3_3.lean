-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T14:02:01.952009+00:00
-- url     : https://prove2.me/submissions/b33da94b-ef6f-431c-8004-c2d1e42fc0e8

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

open ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (p : ℝ) (hp : 0 < p) (hpγ : -γ < p)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ z ∈ box ℓ u, ∀ z' ∈ box ℓ u,
      Mval f p xst z' - Mval f p xst z ≤
        p * inner ℝ (z' - z) (z - xst z) + p * (p / (p + γ) + 1) / 2 * ‖z - z'‖ ^ 2 := by
  intro z _ z' _
  have hle := (hxst z').2 (xst z) (hxst z).1
  have e : ‖xst z - z'‖ ^ 2
      = ‖xst z - z‖ ^ 2 + 2 * inner ℝ (xst z - z) (z - z') + ‖z - z'‖ ^ 2 := by
    have h := norm_add_sq_real (xst z - z) (z - z')
    have h2 : xst z - z + (z - z') = xst z - z' := by abel
    rw [h2] at h
    exact h
  have e2 : inner ℝ (z' - z) (z - xst z) = inner ℝ (xst z - z) (z - z') := by
    have h1 : z' - z = -(z - z') := by abel
    have h2 : z - xst z = -(xst z - z) := by abel
    rw [h1, h2, inner_neg_neg, real_inner_comm]
  have hq : 0 ≤ p / (p + γ) := div_nonneg hp.le (by linarith)
  have hs : 0 ≤ ‖z - z'‖ ^ 2 := by positivity
  have hpos : 0 ≤ p * (p / (p + γ)) / 2 * ‖z - z'‖ ^ 2 := by
    have := mul_nonneg (mul_nonneg hp.le hq) hs
    linarith
  have e3 : p * (p / (p + γ) + 1) / 2 * ‖z - z'‖ ^ 2
      = p * (p / (p + γ)) / 2 * ‖z - z'‖ ^ 2 + p / 2 * ‖z - z'‖ ^ 2 := by ring
  have e4 : p / 2 * ‖xst z - z'‖ ^ 2
      = p / 2 * ‖xst z - z‖ ^ 2 + p * inner ℝ (xst z - z) (z - z') + p / 2 * ‖z - z'‖ ^ 2 := by
    rw [e]; ring
  unfold Mval
  rw [e3, e2]
  linarith

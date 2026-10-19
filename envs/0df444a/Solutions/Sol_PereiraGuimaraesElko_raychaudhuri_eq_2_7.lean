-- Prove2me | solution 1 for PereiraGuimaraesElko.raychaudhuri_eq_2_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:22:21.885628+00:00
-- url     : https://prove2.me/submissions/5f0db67d-5b4e-4851-bd90-ab9f62e60814

import Mathlib

theorem solution (κ : ℝ) (I : Set ℝ) (hI : IsOpen I) (H h Φ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hΦ : ∀ t ∈ I, DifferentiableAt ℝ Φ t)
    (h25 : ∀ t ∈ I, h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * H t) :
    ∀ t ∈ I,
      (deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
          - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
          - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2 ↔
        deriv H t = -(κ ^ 2 / 2) * (1 + κ ^ 2 * Φ t ^ 2 / 8) *
          (deriv Φ t ^ 2 - 1 / 2 * (H t * Φ t * deriv Φ t) / (1 + κ ^ 2 * Φ t ^ 2 / 8) ^ 2)) := by
  intro t ht
  set Dfun : ℝ → ℝ := fun s => 1 + κ ^ 2 * Φ s ^ 2 / 8 with hDfun
  have hDpos : ∀ s, 0 < Dfun s := fun s => by simp only [hDfun]; positivity
  -- (H + h) Φ² = H Φ² / D near t
  have hev : (fun s => (H s + h s) * Φ s ^ 2) =ᶠ[nhds t] fun s => H s * Φ s ^ 2 / Dfun s := by
    filter_upwards [hI.mem_nhds ht] with s hs
    rw [h25 s hs]
    have := hDpos s
    simp only [hDfun] at this ⊢
    field_simp
    ring
  have hDd : HasDerivAt Dfun (κ ^ 2 * (2 * Φ t * deriv Φ t) / 8) t := by
    have := (((hΦ t ht).hasDerivAt.pow 2).const_mul (κ ^ 2)).div_const 8 |>.const_add 1
    refine this.congr_deriv ?_
    push_cast; ring
  have hX : HasDerivAt (fun s => H s * Φ s ^ 2 / Dfun s)
      (((deriv H t * Φ t ^ 2 + H t * (2 * Φ t * deriv Φ t)) * Dfun t
        - H t * Φ t ^ 2 * (κ ^ 2 * (2 * Φ t * deriv Φ t) / 8)) / Dfun t ^ 2) t := by
    have h1 := (hH t ht).hasDerivAt.mul ((hΦ t ht).hasDerivAt.pow 2)
    have h2 := h1.div hDd (hDpos t).ne'
    refine h2.congr_deriv ?_
    push_cast; simp only [Pi.mul_apply, Pi.pow_apply]; ring
  rw [hev.deriv_eq, hX.deriv, h25 t ht]
  have hD := hDpos t
  have hh : 1 + κ ^ 2 * Φ t ^ 2 / 8 = Dfun t := rfl
  rw [hh]
  set H' := deriv H t
  set P := deriv Φ t
  have key : (H' - (-(κ ^ 2 / 2) * (P ^ 2 + 3 / 4 * H t * (-(1 / 8) * (κ ^ 2 * Φ t ^ 2 / Dfun t) * H t) * Φ t ^ 2 -
            1 / 4 * (((H' * Φ t ^ 2 + H t * (2 * Φ t * P)) * Dfun t -
                  H t * Φ t ^ 2 * (κ ^ 2 * (2 * Φ t * P) / 8)) / Dfun t ^ 2)) -
        3 * Dfun t * (-(1 / 8) * (κ ^ 2 * Φ t ^ 2 / Dfun t) * H t) ^ 2)) * Dfun t =
      H' - -(κ ^ 2 / 2) * Dfun t * (P ^ 2 - 1 / 2 * (H t * Φ t * P) / Dfun t ^ 2) := by
    have hD' : 1 + κ ^ 2 * Φ t ^ 2 / 8 ≠ 0 := hD.ne'
    simp only [hDfun] at hD' ⊢
    field_simp
    ring
  constructor
  · intro h1
    have : H' - -(κ ^ 2 / 2) * Dfun t * (P ^ 2 - 1 / 2 * (H t * Φ t * P) / Dfun t ^ 2) = 0 := by
      rw [← key, ← h1]; ring
    linarith
  · intro h1
    have : (H' - (-(κ ^ 2 / 2) * (P ^ 2 + 3 / 4 * H t * (-(1 / 8) * (κ ^ 2 * Φ t ^ 2 / Dfun t) * H t) * Φ t ^ 2 -
            1 / 4 * (((H' * Φ t ^ 2 + H t * (2 * Φ t * P)) * Dfun t -
                  H t * Φ t ^ 2 * (κ ^ 2 * (2 * Φ t * P) / 8)) / Dfun t ^ 2)) -
        3 * Dfun t * (-(1 / 8) * (κ ^ 2 * Φ t ^ 2 / Dfun t) * H t) ^ 2)) * Dfun t = 0 := by
      rw [key]; linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · linarith
    · exact absurd h2 hD.ne'

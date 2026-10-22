-- Prove2me | solution 1 for TokenFinance.Statics.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:35:15.019929+00:00
-- url     : https://prove2.me/submissions/dad76492-1bb3-4824-a7fa-d6bec6acfb2b

import Mathlib
set_option autoImplicit false

theorem solution (c θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    (c / 3 * ((θ - c) / 2 - 0) ^ 2 * (2 * θ + c + 2 * 0) /
        ((c + 0) * θ ^ 2) -
      (θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2) = 0) ∧
    (∀ t : ℝ, -c < t →
      HasDerivAt
        (fun s : ℝ => c / 3 * ((θ - c) / 2 - s) ^ 2 * (2 * θ + c + 2 * s) /
            ((c + s) * θ ^ 2) -
          (θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2))
        (-(c / 3) * (θ - c - 2 * t) * (2 * θ + c + 2 * t) /
            ((c + t) * θ ^ 2) -
          c / 12 * (θ - c - 2 * t) ^ 2 * (2 * θ - c) /
            ((c + t) ^ 2 * θ ^ 2)) t) ∧
    (∀ t : ℝ, 0 ≤ t → t < (θ - c) / 2 →
      (-(c / 3) * (θ - c - 2 * t) * (2 * θ + c + 2 * t) /
          ((c + t) * θ ^ 2) -
        c / 12 * (θ - c - 2 * t) ^ 2 * (2 * θ - c) /
          ((c + t) ^ 2 * θ ^ 2)) < 0) := by
  have hθ : 0 < θ := lt_trans hc hcθ
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · intro t ht
    have hct : 0 < c + t := by linarith
    have h1 : HasDerivAt (fun s : ℝ => (θ - c) / 2 - s) (-1) t :=
      (hasDerivAt_id' t).const_sub _
    have h2 := h1.pow 2
    have h3 : HasDerivAt (fun s : ℝ => 2 * θ + c + 2 * s) 2 t := by
      simpa using ((hasDerivAt_id' t).const_mul 2).const_add (2 * θ + c)
    have h4 : HasDerivAt (fun s : ℝ => (c + s) * θ ^ 2) (θ ^ 2) t := by
      simpa using ((hasDerivAt_id' t).const_add c).mul_const (θ ^ 2)
    have h5 := ((h2.const_mul (c / 3)).mul h3).div h4 (by positivity)
    have h6 := h5.sub_const ((θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2))
    refine h6.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  · intro t ht0 ht1
    have hct : 0 < c + t := by linarith
    have a1 : 0 < θ - c - 2 * t := by linarith
    have a2 : 0 < 2 * θ + c + 2 * t := by linarith
    have a3 : 0 < 2 * θ - c := by linarith
    have e1 : 0 < c / 3 * (θ - c - 2 * t) * (2 * θ + c + 2 * t) / ((c + t) * θ ^ 2) := by positivity
    have e2 : 0 < c / 12 * (θ - c - 2 * t) ^ 2 * (2 * θ - c) / ((c + t) ^ 2 * θ ^ 2) := by positivity
    have : -(c / 3) * (θ - c - 2 * t) * (2 * θ + c + 2 * t) / ((c + t) * θ ^ 2)
        = -(c / 3 * (θ - c - 2 * t) * (2 * θ + c + 2 * t) / ((c + t) * θ ^ 2)) := by ring
    linarith

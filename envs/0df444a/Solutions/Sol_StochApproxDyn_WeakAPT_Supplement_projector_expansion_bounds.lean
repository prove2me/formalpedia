-- Prove2me | solution 1 for StochApproxDyn.WeakAPT.Supplement.projector_expansion_bounds
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T15:27:47.226984+00:00
-- url     : https://prove2.me/submissions/def6de2d-b333-411a-b393-8fd2a2c683e0

import Mathlib

namespace StochApproxDyn.WeakAPT.Supplement
end StochApproxDyn.WeakAPT.Supplement
open StochApproxDyn.WeakAPT.Supplement


theorem solution {m : ℕ}
    (P Pt A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hP : IsIdempotentElem P) (hPt : IsIdempotentElem Pt) (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (h_i : ‖P - Pt‖ ≤ ε) (h_ii : ∀ u, P u = 0 → α * ‖u‖ ≤ ‖A u‖) :
    (∀ v, Pt v = 0 → (α * (1 - ε) - ε * ‖A‖) * ‖v‖ ≤ ‖A v‖) ∧
      ‖Pt * A * (1 - Pt) - P * A * (1 - P)‖ ≤ ε * ‖A‖ * (1 + ‖P‖ + ‖Pt‖) := by
  constructor
  · intro v hv
    have hPP : P (P v) = P v := by
      have := congrArg (fun f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) => f v)
        hP.eq
      simpa using this
    -- project `v` into the kernel of `P`
    have hu : P (v - P v) = 0 := by rw [map_sub, hPP, sub_self]
    have hPv : ‖P v‖ ≤ ε * ‖v‖ := by
      have e : P v = (P - Pt) v := by simp [hv]
      rw [e]
      exact ((P - Pt).le_opNorm v).trans (mul_le_mul_of_nonneg_right h_i (norm_nonneg v))
    have hlow : (1 - ε) * ‖v‖ ≤ ‖v - P v‖ := by
      have := norm_add_le (v - P v) (P v)
      rw [sub_add_cancel] at this
      linarith
    have h1 : α * ((1 - ε) * ‖v‖) ≤ ‖A (v - P v)‖ :=
      (mul_le_mul_of_nonneg_left hlow hα.le).trans (h_ii _ hu)
    have h2 : ‖A (v - P v)‖ ≤ ‖A v‖ + ‖A‖ * (ε * ‖v‖) := by
      rw [map_sub]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      exact (A.le_opNorm (P v)).trans (mul_le_mul_of_nonneg_left hPv (norm_nonneg A))
    have h3 := h1.trans h2
    nlinarith [h3]
  · have e : Pt * A * (1 - Pt) - P * A * (1 - P)
        = (Pt - P) * A * (1 - Pt) + P * A * (P - Pt) := by
      simp only [sub_mul, mul_sub, mul_one]
      abel
    have hone : ‖(1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) - Pt‖
        ≤ 1 + ‖Pt‖ :=
      (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le le_rfl)
    have hd : ‖Pt - P‖ ≤ ε := by rw [norm_sub_rev]; exact h_i
    have hX : ‖(Pt - P) * A * (1 - Pt)‖ ≤ ε * ‖A‖ * (1 + ‖Pt‖) := by
      refine (norm_mul_le _ _).trans ?_
      refine mul_le_mul ((norm_mul_le _ _).trans ?_) hone (norm_nonneg _)
        (mul_nonneg hε.le (norm_nonneg A))
      exact mul_le_mul_of_nonneg_right hd (norm_nonneg A)
    have hY : ‖P * A * (P - Pt)‖ ≤ ‖P‖ * ‖A‖ * ε := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (norm_mul_le _ _) h_i (norm_nonneg _)
        (mul_nonneg (norm_nonneg P) (norm_nonneg A))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add hX hY).trans (le_of_eq ?_))
    ring

-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.inner_sq_add_orth_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T03:46:04.323192+00:00
-- url     : https://prove2.me/submissions/9b110179-68f9-4d71-8cb6-3b1f29f03639

import Mathlib

open InnerProductSpace

/-- `‖u‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2` when `u = c • ξ + w`, `⟨w, ξ⟩ = 0`, `‖ξ‖ = 1`. -/
theorem solution {n : ℕ} (u ξ w : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (hξ : ‖ξ‖ = 1) (hdecomp : u = c • ξ + w) (horth : inner ℝ w ξ = 0) :
    ‖u‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2 := by
  -- Ninth cause-linked repair for `inner_sq_add_orth_sq`, after 7105.
  --
  -- 7105's residual goal was reported *inside `h2`*, not inside `hcore`:
  --
  --   c * 0 + ⟪w, w⟫ = ⟪w, w⟫
  --
  -- `h2 : ⟪w, c • ξ + w⟫ = ⟪w, w⟫` was being closed by
  -- `rw [inner_add_right, real_inner_smul_right, horth]` with no closing tactic. After
  -- `real_inner_smul_left` reduces the `c • ξ` summand of the *first* argument to the
  -- product `c * ⟪w, ξ⟫`, rewriting by `horth` leaves `c * 0` rather than `0`, so the
  -- goal is a ring identity that the `rw` alone cannot close. 7098 and 7090 failed at
  -- the same step for the same reason.
  --
  -- This repair adds the missing closer to `h2` (`ring`, which normalises `c * 0`) and
  -- leaves `hcore` exactly as 7105 had it.
  have hxiw : inner ℝ ξ w = 0 := by
    simpa only [real_inner_comm] using horth
  have hξξ : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  -- `⟪ξ, c • ξ + w⟫ = c * ⟪ξ, ξ⟫ + ⟪ξ, w⟫ = c`.
  have h1 : inner ℝ ξ (c • ξ + w) = c := by
    rw [inner_add_right, real_inner_smul_right, hξξ, hxiw]
    ring
  -- `⟪w, c • ξ + w⟫ = c * ⟪w, ξ⟫ + ⟪w, w⟫ = ⟪w, w⟫`.  The trailing `ring` is the whole
  -- fix: it is what reduces the `c * 0` that `rw [... , horth]` leaves behind.
  have h2 : inner ℝ w (c • ξ + w) = inner ℝ w w := by
    rw [inner_add_right, real_inner_smul_right, horth]
    ring
  have hsplit : inner ℝ (c • ξ + w) (c • ξ + w)
      = c * inner ℝ ξ (c • ξ + w) + inner ℝ w (c • ξ + w) := by
    rw [inner_add_left, real_inner_smul_left]
  have hcore : inner ℝ (c • ξ + w) (c • ξ + w) = c ^ 2 + inner ℝ w w := by
    rw [hsplit, h1, h2]
    ring_nf
  rw [hdecomp, ← real_inner_self_eq_norm_sq, hcore, real_inner_self_eq_norm_sq]

-- Prove2me | solution 1 for PGDMap20261031.pgd_full_curve
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:29.981086+00:00
-- url     : https://prove2.me/submissions/fb50a593-7f1e-4d6c-8e8f-eede8c8a132f

import Mathlib.Tactic
import Theorems.Thm_PGDMap20261031_pgd_best_modulus
import Theorems.Thm_PGDMap20261031_pgd_uniform_upper
import Theorems.Thm_PGDMap20261031_pgd_quadratic_attainment
import Theorems.Thm_PGDMap20261031_pgd_fixed_penalty_sharpness
open PGDMap20261031

theorem solution : FullCurveTheorem := by
  have upper := PGDMap20261031.pgd_uniform_upper
  have matching := PGDMap20261031.pgd_quadratic_attainment
  refine ⟨?_, upper, matching⟩
  intro d r L h N hr hnon hL hh hN
  obtain ⟨hmu, hstrong⟩ := PGDMap20261031.pgd_best_modulus d r hr hnon
  constructor
  · intro v hv
    obtain ⟨f, g, x, hsmooth, htraj, hdec, rfl⟩ := hv
    apply (div_le_iff₀ (mul_pos hL hdec)).mpr
    have bound := upper d r L (bestModulus r) h N f g x
      hr hL hmu hstrong hh hN hsmooth htraj
    simpa only [mul_assoc, mul_left_comm, mul_comm] using bound
  · intro b hb
    by_contra hnot
    have hbsmall : b < curve N h (bestModulus r / L) := lt_of_not_ge hnot
    obtain ⟨v, hv, hvlarge⟩ := PGDMap20261031.pgd_fixed_penalty_sharpness
      d r L h N hr hnon hL hh hN
      ((curve N h (bestModulus r / L) - b) / 2) (by linarith)
    have hvsmall := hb hv
    linarith

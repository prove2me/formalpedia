-- Prove2me | solution 1 for PrivLearn.MaskedParity.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:50.126211+00:00
-- url     : https://prove2.me/submissions/816ac201-44af-481e-b923-719320dd8960

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle
set_option autoImplicit false
open PrivLearn.MaskedParity

theorem solution {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) :
    qval (cMP r a) g =
      Cg g + ip (half 0 (fg g)) (half 0 (cMP r a)) + ip (half 1 (fg g)) (half 1 (cMP r a)) := by
  have hpt : ∀ u : Dom d, g u (cMP r a u) =
      (g u 1 + g u (-1)) / 2 + (half 0 (fg g) u * half 0 (cMP r a) u + half 1 (fg g) u * half 1 (cMP r a) u) := by
    intro u
    have hc : cMP r a u = 1 ∨ cMP r a u = -1 := by
      unfold cMP
      split_ifs
      · exact (neg_one_pow_eq_or ℝ _).imp id id
      · exact (neg_one_pow_eq_or ℝ _).imp id id
    have hb : u.2.2 = 0 ∨ u.2.2 = 1 := by
      generalize u.2.2 = b
      revert b; decide
    rcases hb with hb | hb
    · have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [half, hb, h01]
      unfold fg
      rcases hc with hc | hc <;> rw [hc] <;> ring
    · have h10 : (1 : ZMod 2) ≠ 0 := by decide
      simp [half, hb, h10]
      unfold fg
      rcases hc with hc | hc <;> rw [hc] <;> ring
  unfold qval Cg ip
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

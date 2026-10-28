-- Prove2me | solution 1 for ThirdLawThermo.boltzmannEntropy_one_eq_zero_and_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:11:43.059376+00:00
-- url     : https://prove2.me/submissions/91250043-db03-4839-a238-bf21c413b0fc

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology
open ThirdLawThermo

theorem solution (kB : ℝ) (hkB : 0 < kB) :
    boltzmannEntropy kB 1 = 0 ∧ ∀ W : ℕ, 1 < W → 0 < boltzmannEntropy kB W := by
  refine ⟨by simp [boltzmannEntropy], fun W hW => ?_⟩
  unfold boltzmannEntropy
  apply mul_pos hkB
  apply Real.log_pos
  exact_mod_cast hW

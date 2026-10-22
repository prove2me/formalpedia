-- Prove2me | solution 1 for Tegmark.tachyon_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:07:26.427266+00:00
-- url     : https://prove2.me/submissions/948fef89-af6d-4e7f-bfd1-bae7b4dbd017

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
open Tegmark

theorem solution (n m : ℕ) : pdeClass n m = pdeClass m n := by
  unfold pdeClass
  by_cases h0 : n = 0 ∨ m = 0
  · rw [if_pos h0, if_pos (Or.symm h0)]
  · rw [if_neg h0, if_neg (fun h => h0 (Or.symm h))]
    by_cases h1 : n = 1 ∨ m = 1
    · rw [if_pos h1, if_pos (Or.symm h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (Or.symm h))]

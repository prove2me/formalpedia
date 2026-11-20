-- Prove2me | solution 1 for Sensitivity.flipBit_flipBit_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:55:48.497046+00:00
-- url     : https://prove2.me/submissions/f573bca7-3f47-4c9f-aa35-b47c6bbed931

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_apply_ne

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (x : Fin n → Bool) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  ext j
  by_cases h : j = i
  · subst h; simp [flipBit, Bool.not_not]
  · simp [flipBit, Function.update_of_ne h]
end Sensitivity

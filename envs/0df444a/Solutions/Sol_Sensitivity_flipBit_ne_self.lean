-- Prove2me | solution 1 for Sensitivity.flipBit_ne_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:56:14.13594+00:00
-- url     : https://prove2.me/submissions/67e62326-6199-49e4-8428-af902d5706ad

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_flipBit_same

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (x : Fin n → Bool) (i : Fin n) :
    flipBit x i ≠ x := by
  intro h
  have := congr_fun h i
  simp [flipBit] at this
end Sensitivity

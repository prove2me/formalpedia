-- Prove2me | solution 1 for Sensitivity.flipBit_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:56:14.632179+00:00
-- url     : https://prove2.me/submissions/e8b8fcc4-ea63-4713-a7fe-66542fbf5257

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
theorem _root_.solution (x : Fin n → Bool) : Function.Injective (flipBit x) := by
  intro i j hij
  by_contra h
  push_neg at h
  have h1 : flipBit x i i = !x i := flipBit_apply_same x i
  have h2 : flipBit x j i = x i := flipBit_apply_ne x j h
  rw [congr_fun hij i, h2] at h1
  simp at h1
end Sensitivity

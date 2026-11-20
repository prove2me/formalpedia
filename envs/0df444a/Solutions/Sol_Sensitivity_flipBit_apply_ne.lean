-- Prove2me | solution 1 for Sensitivity.flipBit_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:55:12.805659+00:00
-- url     : https://prove2.me/submissions/1cd1b2e6-d4da-4a94-8d2a-173f01e42541

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
import Theorems.Thm_Sensitivity_flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_apply_same

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (x : Fin n → Bool) (i : Fin n) {j : Fin n} (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, Function.update_of_ne h]
end Sensitivity

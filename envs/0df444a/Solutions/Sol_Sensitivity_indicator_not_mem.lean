-- Prove2me | solution 1 for Sensitivity.indicator_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:56:48.444536+00:00
-- url     : https://prove2.me/submissions/bc7444c8-f9ed-4b1b-94d3-f52a1947893a

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same


attribute [local simp] Sensitivity.indicator_mem

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = false ↔ i ∉ S := by
  simp [indicator]
end Sensitivity

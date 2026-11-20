-- Prove2me | solution 1 for Sensitivity.indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:56:13.509574+00:00
-- url     : https://prove2.me/submissions/a8832a12-06b8-4fcd-836f-592bb9047095

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = true ↔ i ∈ S := by
  simp [indicator]
end Sensitivity

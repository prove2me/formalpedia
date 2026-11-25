-- Prove2me | solution 1 for PretorsionImageClosed.Statement.deltaXPow_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:55.634477+00:00
-- url     : https://prove2.me/submissions/8a0e20f7-b96e-4762-a6f0-90ba2a8b0e3d

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial
namespace PretorsionImageClosed.Statement
theorem _root_.solution (m : ℕ) : deltaXPow (m + 2) = X ^ (m + 1) + U * deltaXPow (m + 1) := by
  show geomSum (m + 1) = X ^ (m + 1) + U * geomSum m
  rw [geomSum_succ, add_comm]
end PretorsionImageClosed.Statement

-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isDelta_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:39.653016+00:00
-- url     : https://prove2.me/submissions/54042c1a-410e-40e8-aa64-bb74eb2f1713

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
theorem _root_.solution : IsDelta (0 : Rq[X]) 0 := by
  unfold IsDelta
  simp
end PretorsionImageClosed.Statement

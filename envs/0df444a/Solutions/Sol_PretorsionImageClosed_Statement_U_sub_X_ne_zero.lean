-- Prove2me | solution 1 for PretorsionImageClosed.Statement.U_sub_X_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:56.61199+00:00
-- url     : https://prove2.me/submissions/077d3dcf-24f2-4c49-8f1f-5b2522f13777

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
theorem _root_.solution : (U - X : Rq[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : Rq[X] => p.coeff 0) h
  simp at this
end PretorsionImageClosed.Statement

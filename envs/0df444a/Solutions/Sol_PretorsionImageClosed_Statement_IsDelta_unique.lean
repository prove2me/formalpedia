-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsDelta.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:45.669288+00:00
-- url     : https://prove2.me/submissions/3d5d3c85-9a1a-465f-9007-ce1ed68d6a58

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Theorems.Thm_PretorsionImageClosed_Statement_U_sub_X_ne_zero

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial
namespace PretorsionImageClosed.Statement
namespace IsDelta
theorem _root_.solution {f g g' : Rq[X]} (h : IsDelta f g) (h' : IsDelta f g') : g = g' := by
  unfold IsDelta at h h'
  rw [one_add_C_sub_mul_X] at h h'
  exact mul_right_cancel₀ U_sub_X_ne_zero (h.trans h'.symm)
end IsDelta
end PretorsionImageClosed.Statement

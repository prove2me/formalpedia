-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isDelta_X_mul_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:36.538568+00:00
-- url     : https://prove2.me/submissions/494a9e84-e20f-4aa7-b71b-39cafce3d6bb

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
theorem _root_.solution {g G : Rq[X]} (hG : IsDelta g G) :
    IsDelta (X * g.comp U) (g.comp U + C q * U * G.comp U) := by
  unfold IsDelta at *
  have hG' := congrArg (fun p : Rq[X] => p.comp U) hG
  simp only [mul_comp, add_comp, one_comp, C_comp, C_mul_comp, X_comp, sub_comp, comp_assoc] at hG'
  simp only [mul_comp, add_comp, one_comp, C_comp, C_mul_comp, X_comp, sub_comp, comp_assoc]
  rw [C_sub, C_1] at hG' ⊢
  linear_combination (1 + C q * X) * hG'
end PretorsionImageClosed.Statement

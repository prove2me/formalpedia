-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.finrank_intervalSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:58:54.004742+00:00
-- url     : https://prove2.me/submissions/a3ce0b80-9c2f-48e2-94f1-9b4d0e249e57

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSpace_of_mem

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k]
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (a d i : Fin n) :
    Module.finrank k (intervalSpace k a d i) = if a ≤ i ∧ i ≤ d then 1 else 0 := by
  by_cases h : a ≤ i ∧ i ≤ d
  · rw [intervalSpace_of_mem k h, if_pos h, finrank_top, Module.finrank_self]
  · rw [intervalSpace_of_not_mem k h, if_neg h, finrank_bot]
end PretorsionImageClosed.LinearQuiver

-- Prove2me | solution 1 for Potential.closedPaths_iff_actualClosedPaths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:02:38.789+00:00
-- url     : https://prove2.me/submissions/fcb95646-6401-4d6e-85a9-badc71e96d1f

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_remove_noop_moves

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (u : Payoff A) :
    ClosedPathProperty u ↔ ActualClosedPathProperty u := by
  constructor
  · intro h s ms _ he
    exact h s ms he
  · intro h s ms he
    obtain ⟨ns, hn, he', hv⟩ := remove_noop_moves u s ms
    rw [← hv]
    exact h s ns hn (he'.trans he)
end Potential

-- Prove2me | solution 1 for Stallings.InverseAutomaton.run_eq_some_iff_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:52.50939+00:00
-- url     : https://prove2.me/submissions/4e2d7cef-6d89-4b70-af92-5b448f43e434

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution {v z : V} {w : Word} :
    G.run v w = some z ↔ G.Walk v w z := by
  induction w generalizing v z with
  | nil =>
      simp only [run, Option.some.injEq]
      constructor
      · intro h
        subst z
        exact Walk.nil v
      · intro h
        cases h
        rfl
  | cons x w ih =>
      constructor
      · intro h
        cases hnext : G.next v x with
        | none => simp [run, hnext] at h
        | some u =>
            simp [run, hnext] at h
            exact Walk.cons hnext ((ih (v := u) (z := z)).mp h)
      · intro h
        cases h with
        | cons hnext htail =>
            simp [run, hnext, (ih (v := _) (z := _)).mpr htail]
end Stallings.InverseAutomaton

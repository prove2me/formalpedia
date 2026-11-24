-- Prove2me | solution 1 for Stallings.InverseAutomaton.run_success_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:47.918729+00:00
-- url     : https://prove2.me/submissions/738db47b-c171-4d41-9dfc-5b3cf1f78a6e

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
import Theorems.Thm_Stallings_InverseAutomaton_run_append

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution (v : V) (pre suffix : Word) (x : Letter)
    {z : V}
    (h : G.run v (pre ++ x :: letterInv x :: suffix) = some z) :
    G.run v (pre ++ suffix) = some z := by
  rw [G.run_append v pre (x :: letterInv x :: suffix)] at h
  rw [G.run_append v pre suffix]
  cases hp : G.run v pre with
  | none => simp [hp] at h
  | some s =>
      rw [hp] at h
      change G.run s (x :: letterInv x :: suffix) = some z at h
      change G.run s suffix = some z
      cases he : G.next s x with
      | none => simp [run, he] at h
      | some t =>
          have ht : G.next t (letterInv x) = some s := G.inverse_next he
          simpa [run, he, ht] using h
end Stallings.InverseAutomaton

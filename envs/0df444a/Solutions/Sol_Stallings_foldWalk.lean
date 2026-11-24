-- Prove2me | solution 1 for Stallings.foldWalk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:52.770799+00:00
-- url     : https://prove2.me/submissions/fea1da8b-60d1-45d5-bd5d-e01fe7b89a1f

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_foldedNext_of_edge
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (base v z : V)
    {w : Word} (h : G.Walk v w z) :
    (foldAutomaton G base).run (foldRep G v) w = some (foldRep G z) := by
  induction h with
  | nil v => rfl
  | @cons v u z x w edge tail ih =>
      simp only [InverseAutomaton.run]
      change ((foldedNext G (foldRep G v) x).bind
        fun q => (foldAutomaton G base).run q w) = some (foldRep G z)
      rw [foldedNext_of_edge G edge]
      exact ih
end Stallings

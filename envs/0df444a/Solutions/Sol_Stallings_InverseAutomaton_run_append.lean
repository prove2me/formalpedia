-- Prove2me | solution 1 for Stallings.InverseAutomaton.run_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:53.007714+00:00
-- url     : https://prove2.me/submissions/757e1a2e-bddd-40d3-9587-66088d6e6700

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution (v : V) (u z : Word) :
    G.run v (u ++ z) = (G.run v u).bind fun t => G.run t z := by
  induction u generalizing v with
  | nil => rfl
  | cons x u ih =>
      change (G.next v x).bind (fun t => G.run t (u ++ z)) =
        ((G.next v x).bind (fun t => G.run t u)).bind (fun t => G.run t z)
      calc
        _ = (G.next v x).bind (fun t => (G.run t u).bind fun q => G.run q z) := by
          congr 1
          funext t
          exact ih t
        _ = _ := (Option.bind_assoc _ _ _).symm
end Stallings.InverseAutomaton

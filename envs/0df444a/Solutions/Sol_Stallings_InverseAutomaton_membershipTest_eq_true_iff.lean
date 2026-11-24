-- Prove2me | solution 1 for Stallings.InverseAutomaton.membershipTest_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:37.034814+00:00
-- url     : https://prove2.me/submissions/83bc9e54-967a-4a00-9ba4-e32a66848d45

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
import Theorems.Thm_Stallings_InverseAutomaton_accepts_iff_mem_loopSubgroup

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution [DecidableEq V] (G : InverseAutomaton V) (g : Free) :
    G.membershipTest g = true ↔ g ∈ G.loopSubgroup := by
  simpa [membershipTest, accepts] using G.accepts_iff_mem_loopSubgroup g
end Stallings.InverseAutomaton

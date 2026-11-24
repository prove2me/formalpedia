-- Prove2me | solution 1 for Stallings.InverseAutomaton.accepts_iff_mem_loopSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:02.785059+00:00
-- url     : https://prove2.me/submissions/4a89fe0e-1d8a-4b6d-997a-0a066a8abf11

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
import Theorems.Thm_Stallings_InverseAutomaton_run_eq_some_iff_walk
import Theorems.Thm_Stallings_InverseAutomaton_run_success_of_reduction

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution (g : Free) :
    G.accepts g ↔ g ∈ G.loopSubgroup := by
  constructor
  · intro h
    refine ⟨FreeGroup.toWord g, ?_, (run_eq_some_iff_walk G).mp h⟩
    simpa [wordEval] using (FreeGroup.mk_toWord (x := g))
  · rintro ⟨w, hw, hwalk⟩
    have evalCanonical : wordEval (FreeGroup.toWord g) = g := by
      simpa [wordEval] using (FreeGroup.mk_toWord (x := g))
    have evalEq : wordEval w = wordEval (FreeGroup.toWord g) := hw.trans evalCanonical.symm
    have hrun : G.run G.base w = some G.base :=
      (run_eq_some_iff_walk G).2 hwalk
    have hred : G.run G.base (FreeGroup.reduce w) = some G.base :=
      G.run_success_of_reduction G.base w hrun
    have reducedEq : FreeGroup.reduce w = FreeGroup.reduce (FreeGroup.toWord g) := by
      apply FreeGroup.reduce.sound
      simpa [wordEval] using evalEq
    have hcanonical : G.run G.base (FreeGroup.reduce (FreeGroup.toWord g)) = some G.base := by
      rw [← reducedEq]
      exact hred
    simpa [accepts] using hcanonical
end Stallings.InverseAutomaton

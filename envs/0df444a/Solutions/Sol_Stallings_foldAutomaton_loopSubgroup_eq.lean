-- Prove2me | solution 1 for Stallings.foldAutomaton_loopSubgroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:15:43.688272+00:00
-- url     : https://prove2.me/submissions/ff720910-fa50-4285-b3df-001f698e62b2

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_foldWalk
import Theorems.Thm_Stallings_CosetEquivalent_mem_of_mem_and_rel
import Theorems.Thm_Stallings_foldRel_cosetPotential
import Theorems.Thm_Stallings_run_cosetPotential
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
import Theorems.Thm_Stallings_InverseAutomaton_run_eq_some_iff_walk
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (base : V) (potential : V → Free)
    (hpotential : HasCosetPotential G (G.loopSubgroup base) potential)
    (hbase : potential base = 1) :
    (foldAutomaton G base).loopSubgroup = G.loopSubgroup base := by
  apply le_antisymm
  · intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    have hrun : (foldAutomaton G base).run (foldRep G base) w = some (foldRep G base) :=
      (InverseAutomaton.run_eq_some_iff_walk (foldAutomaton G base)).2 hwalk
    have hword := run_cosetPotential G base (G.loopSubgroup base) potential hpotential hrun
    have hrepBase : potential (foldRep G base) ∈ G.loopSubgroup base := by
      have hcoset : CosetEquivalent (G.loopSubgroup base) (potential (foldRep G base)) 1 := by
        simpa [hbase] using foldRel_cosetPotential G (G.loopSubgroup base) potential hpotential
          (foldRep_rel G base)
      simpa [CosetEquivalent] using hcoset
    have hprod : potential (foldRep G base) * wordEval w ∈ G.loopSubgroup base :=
      CosetEquivalent.mem_of_mem_and_rel hword hrepBase
    have hwordMem : wordEval w ∈ G.loopSubgroup base := by
      have := (G.loopSubgroup base).mul_mem ((G.loopSubgroup base).inv_mem hrepBase) hprod
      simpa [mul_assoc] using this
    rw [← hw]
    exact hwordMem
  · change Subgroup.closure
      {g : Free | ∃ w : Word, wordEval w = g ∧ G.Walk base w base} ≤
      (foldAutomaton G base).loopSubgroup
    apply (Subgroup.closure_le ((foldAutomaton G base).loopSubgroup)).2
    intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    refine ⟨w, hw, ?_⟩
    have hfold := foldWalk G base base base hwalk
    exact (InverseAutomaton.run_eq_some_iff_walk (foldAutomaton G base)).mp hfold
end Stallings

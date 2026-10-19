-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.card_filter_permutationGraph_fst_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/04c9c4b9-4000-4181-b60b-d24e56b0d7af

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_mem_permutationGraph

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    ((SoficGroups.permutationGraph p).filter
      fun z => z.1 ∈ B).card = B.card := by
  classical
  apply Finset.card_bij (fun z _ => z.1)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz w hw hfirst
    have hzgraph := (Finset.mem_filter.mp hz).1
    have hwgraph := (Finset.mem_filter.mp hw).1
    have hzsecond :=
      (SoficGroups.mem_permutationGraph p z.1 z.2).mp hzgraph
    have hwsecond :=
      (SoficGroups.mem_permutationGraph p w.1 w.2).mp hwgraph
    apply Prod.ext hfirst
    simpa [hzsecond, hwsecond] using congrArg p hfirst
  · intro x hx
    refine ⟨(x, p x), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨(SoficGroups.mem_permutationGraph p x (p x)).mpr rfl, hx⟩
end SoficGroups.KunDiagonalGoodRootGraphLoss

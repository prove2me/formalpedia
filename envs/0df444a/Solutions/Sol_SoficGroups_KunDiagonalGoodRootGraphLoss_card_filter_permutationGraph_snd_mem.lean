-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.card_filter_permutationGraph_snd_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/3105f386-b662-4bdb-a4fc-cfa843e8c733

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
      fun z => z.2 ∈ B).card = B.card := by
  classical
  apply Finset.card_bij (fun z _ => z.2)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz w hw hsecond
    have hzgraph := (Finset.mem_filter.mp hz).1
    have hwgraph := (Finset.mem_filter.mp hw).1
    have hzsecond :=
      (SoficGroups.mem_permutationGraph p z.1 z.2).mp hzgraph
    have hwsecond :=
      (SoficGroups.mem_permutationGraph p w.1 w.2).mp hwgraph
    apply Prod.ext
    · apply p.injective
      simpa [hzsecond, hwsecond] using hsecond
    · exact hsecond
  · intro y hy
    refine ⟨(p.symm y, y), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hy⟩
    apply (SoficGroups.mem_permutationGraph p (p.symm y) y).mpr
    simp
end SoficGroups.KunDiagonalGoodRootGraphLoss

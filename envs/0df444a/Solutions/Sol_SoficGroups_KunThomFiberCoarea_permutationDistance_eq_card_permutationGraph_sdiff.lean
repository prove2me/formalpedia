-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationDistance_eq_card_permutationGraph_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/c0db5062-8b79-4d2e-bce1-c2ccefaf4b8f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_mem_permutationGraph

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) :
    SoficGroups.permutationDistance p q =
      (SoficGroups.permutationGraph p \
        SoficGroups.permutationGraph q).card := by
  classical
  unfold SoficGroups.permutationDistance hammingDist
  apply Finset.card_bij (fun x _ => (x, p x))
  · intro x hx
    obtain ⟨_, hne⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨(SoficGroups.mem_permutationGraph p x (p x)).mpr rfl, ?_⟩
    intro hxq
    exact hne ((SoficGroups.mem_permutationGraph q x (p x)).mp hxq)
  · intro x _ y _ h
    exact congrArg Prod.fst h
  · intro z hz
    obtain ⟨hzp, hzq⟩ := Finset.mem_sdiff.mp hz
    have hzsecond :=
      (SoficGroups.mem_permutationGraph p z.1 z.2).mp hzp
    refine ⟨z.1, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      apply hzq
      exact (SoficGroups.mem_permutationGraph q z.1 z.2).mpr
        (hzsecond.trans heq)
    · exact Prod.ext rfl hzsecond.symm
end SoficGroups.KunThomFiberCoarea

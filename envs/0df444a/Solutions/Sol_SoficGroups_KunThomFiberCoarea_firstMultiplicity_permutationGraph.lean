-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstMultiplicity_permutationGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/7232d51a-3b11-497c-ac19-a9e9f5413b75

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
    (p : Equiv.Perm V) (x : V) :
    firstMultiplicity (SoficGroups.permutationGraph p) x = 1 := by
  classical
  have hset :
      firstFiber (SoficGroups.permutationGraph p) x =
        {(x, p x)} := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzgraph, hzfirst⟩ := Finset.mem_filter.mp hz
      have hzsecond :=
        (SoficGroups.mem_permutationGraph p z.1 z.2).mp hzgraph
      apply Finset.mem_singleton.mpr
      apply Prod.ext hzfirst
      exact hzsecond.trans (congrArg p hzfirst)
    · intro hz
      have heq := Finset.mem_singleton.mp hz
      subst z
      apply Finset.mem_filter.mpr
      exact ⟨(SoficGroups.mem_permutationGraph p x (p x)).mpr rfl,
        rfl⟩
  unfold firstMultiplicity
  rw [hset]
  simp
end SoficGroups.KunThomFiberCoarea

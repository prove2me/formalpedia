-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondMultiplicity_permutationGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/128abadd-48b7-43d7-bd96-114fc426887a

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
    secondMultiplicity (SoficGroups.permutationGraph p) x = 1 := by
  classical
  have hset :
      secondFiber (SoficGroups.permutationGraph p) x =
        {(p.symm x, x)} := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzgraph, hzsecond⟩ := Finset.mem_filter.mp hz
      have hgraph :=
        (SoficGroups.mem_permutationGraph p z.1 z.2).mp hzgraph
      apply Finset.mem_singleton.mpr
      apply Prod.ext
      · apply p.injective
        simpa using hgraph.symm.trans hzsecond
      · exact hzsecond
    · intro hz
      have heq := Finset.mem_singleton.mp hz
      subst z
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      exact (SoficGroups.mem_permutationGraph p (p.symm x) x).mpr
        (p.apply_symm_apply x).symm
  unfold secondMultiplicity
  rw [hset]
  simp
end SoficGroups.KunThomFiberCoarea

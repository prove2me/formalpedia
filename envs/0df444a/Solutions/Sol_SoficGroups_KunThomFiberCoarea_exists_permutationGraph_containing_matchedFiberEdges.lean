-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.exists_permutationGraph_containing_matchedFiberEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/f440da29-b7b9-46f6-86eb-21aecff864f0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_mem_permutationGraph
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_exists_permutation_extending_matchedFiberEdges

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    ∃ p : Equiv.Perm V,
      matchedFiberEdges U ⊆ SoficGroups.permutationGraph p := by
  obtain ⟨p, hp⟩ := exists_permutation_extending_matchedFiberEdges U
  refine ⟨p, ?_⟩
  intro z hz
  have h :=
    (SoficGroups.mem_permutationGraph p z.1 z.2).mpr (hp z hz).symm
  simpa only [Prod.mk.eta] using h
end SoficGroups.KunThomFiberCoarea

-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationGraph_sdiff_bounds_of_matchedFiberEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/7a6ef1f8-3609-48b2-9692-18c136f1cd8b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationGraph_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V)
    (hp : matchedFiberEdges U ⊆ SoficGroups.permutationGraph p) :
    (SoficGroups.permutationGraph p \ U).card ≤
        Fintype.card V - (matchedFiberEdges U).card ∧
      (U \ SoficGroups.permutationGraph p).card ≤
        (U \ matchedFiberEdges U).card := by
  classical
  have hGU : matchedFiberEdges U ⊆ U := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hleftsub :
      matchedFiberEdges U ⊆ U ∩ SoficGroups.permutationGraph p := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hGU hz, hp hz⟩
  have hrightsub :
      matchedFiberEdges U ⊆ SoficGroups.permutationGraph p ∩ U := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hp hz, hGU hz⟩
  have hleftcard := Finset.card_le_card hleftsub
  have hrightcard := Finset.card_le_card hrightsub
  have hgraph := permutationGraph_card p
  have hleft := Finset.card_sdiff_add_card_inter
    (SoficGroups.permutationGraph p) U
  have hright := Finset.card_sdiff_add_card_inter
    U (SoficGroups.permutationGraph p)
  have hmatched := Finset.card_sdiff_add_card_inter U (matchedFiberEdges U)
  have hinter :
      (U ∩ matchedFiberEdges U).card =
        (matchedFiberEdges U).card := by
    have hset : U ∩ matchedFiberEdges U = matchedFiberEdges U := by
      exact Finset.inter_eq_right.mpr hGU
    rw [hset]
  have hswap :
      (U ∩ SoficGroups.permutationGraph p).card =
        (SoficGroups.permutationGraph p ∩ U).card := by
    rw [Finset.inter_comm]
  constructor <;> omega
end SoficGroups.KunThomFiberCoarea

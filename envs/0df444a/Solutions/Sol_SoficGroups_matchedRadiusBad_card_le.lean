-- Prove2me | solution 1 for SoficGroups.matchedRadiusBad_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/a438c8f6-a6a9-40d0-bebe-3c2c74a7ae8b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (I : Finset ι) (w : ι → Equiv.Perm V)
    (B : Finset V) :
    (U ∩ matchedRadiusBad P I w B).card ≤
      (U ∩ B).card +
        ∑ i ∈ I, (partitionWordCrossing P (w i)).card := by
  have hsubset : U ∩ matchedRadiusBad P I w B ⊆
      (U ∩ B) ∪ I.biUnion (fun i => partitionWordCrossing P (w i)) := by
    intro x hx
    obtain ⟨hxU, hx⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hx with hxB | hxW
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hxB⟩)
    · exact Finset.mem_union_right _ hxW
  have hfirst := Finset.card_le_card hsubset
  have hsecond := Finset.card_union_le
    (U ∩ B) (I.biUnion fun i => partitionWordCrossing P (w i))
  have hthird := Finset.card_biUnion_le
    (s := I) (t := fun i => partitionWordCrossing P (w i))
  omega
end SoficGroups

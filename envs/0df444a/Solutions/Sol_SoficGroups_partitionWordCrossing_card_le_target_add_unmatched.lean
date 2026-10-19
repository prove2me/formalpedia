-- Prove2me | solution 1 for SoficGroups.partitionWordCrossing_card_le_target_add_unmatched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/5291d905-8312-42e9-8ee0-397e22a7467a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedWordPreimageBad_card_le
import Theorems.Thm_SoficGroups_partitionWordCrossing_subset_target_or_unmatched

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (w : Equiv.Perm V) :
    (partitionWordCrossing P w).card ≤
      (partitionWordCrossing Q w).card +
        2 * (U \ matchedCore R D).card := by
  have hsub := Finset.card_le_card
    (partitionWordCrossing_subset_target_or_unmatched
      P Q R hR D hD hinj w)
  have hfirst := Finset.card_union_le
    (partitionWordCrossing Q w) (U \ matchedCore R D)
  have hsecond := Finset.card_union_le
    (partitionWordCrossing Q w ∪ (U \ matchedCore R D))
    (matchedWordPreimageBad U R D w)
  have hpre := matchedWordPreimageBad_card_le U R D w
  omega
end SoficGroups

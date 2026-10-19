-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_sourceExceptionalBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/3a3c6b09-4505-493b-988e-c3478875404d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceRowBlock_card
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_exceptionalBlockProduct
import Theorems.Thm_PermanentRollout_sourceRowBlock_biUnion_erase

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t d : ℕ) (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d) (h : Fin b) :
    squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (squareZeroBlockSum (b * t) (sourceRowBlock b t h) ^ (t - d) *
          ∏ j ∈ (Finset.univ : Finset (Fin b)).erase h,
            squareZeroBlockSum (b * t) (sourceRowBlock b t j) ^ t) =
      if omitted ⊆ sourceRowBlock b t h then
        ((t.factorial ^ (b - 1) : ℕ) : ℂ) *
          (((t - d).factorial : ℕ) : ℂ)
      else 0 := by
  classical
  have hdisjoint : Set.PairwiseDisjoint
      (↑((Finset.univ : Finset (Fin b)).erase h))
      (sourceRowBlock b t) := by
    intro left _ right _ hne
    exact sourceRowBlock_disjoint hne
  rw [squareZeroCoefficient_exceptionalBlockProduct
    (sourceRowBlock b t)
    ((Finset.univ : Finset (Fin b)).erase h)
    h t d ((Finset.univ : Finset (Fin (b * t))) \ omitted)
    (fun j _ => sourceRowBlock_card b t j) hdisjoint,
    sourceRowBlock_biUnion_erase]
  have hremaining :
      ((Finset.univ : Finset (Fin (b * t))) \ omitted) \
          ((Finset.univ : Finset (Fin (b * t))) \
            sourceRowBlock b t h) =
        sourceRowBlock b t h \ omitted := by
    ext row
    simp [and_comm]
  rw [hremaining]
  have hsubset_equiv :
      (Finset.univ \ sourceRowBlock b t h) ⊆
          (Finset.univ \ omitted) ↔
        omitted ⊆ sourceRowBlock b t h :=
    Finset.sdiff_subset_sdiff_iff_subset
      (Finset.subset_univ (sourceRowBlock b t h))
      (Finset.subset_univ omitted)
  by_cases hsubset : omitted ⊆ sourceRowBlock b t h
  · have hfirst := hsubset_equiv.mpr hsubset
    have hcard :
        (sourceRowBlock b t h \ omitted).card = t - d := by
      rw [Finset.card_sdiff_of_subset hsubset,
        sourceRowBlock_card, homitted]
    simp [hsubset, hfirst, hcard]
  · have hfirst :
        ¬(Finset.univ \ sourceRowBlock b t h) ⊆
          (Finset.univ \ omitted) :=
        fun hfirst => hsubset (hsubset_equiv.mp hfirst)
    simp [hsubset, hfirst]
end PermanentRollout

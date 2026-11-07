-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.checkSetNeighborhood_eq_iff_groupedExactNeighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:56:04.532201+00:00
-- url     : https://prove2.me/submissions/abf3b61f-fc7c-4d2c-a781-fe2a2861b28e

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    checkSetNeighborhood sample S = T ↔
      GroupedExactNeighborhood S T (sampleEquivGrouped r sample) := by
  constructor
  · intro h b
    by_cases hbT : b ∈ T
    · rw [if_pos hbT]
      rw [← h] at hbT
      have hbCount := (Finset.mem_filter.mp hbT).2
      have hNonempty :
          (S.filter fun a => sample (a, b)).Nonempty :=
        Finset.card_pos.mp hbCount
      rcases hNonempty with ⟨a, ha⟩
      exact ⟨a, (Finset.mem_filter.mp ha).1,
        (Finset.mem_filter.mp ha).2⟩
    · rw [if_neg hbT]
      intro a
      by_cases haS : a ∈ S
      · rw [if_pos haS]
        apply Bool.eq_false_iff.mpr
        intro haTrue
        have hbNeighborhood : b ∈ checkSetNeighborhood sample S := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          apply Finset.card_pos.mpr
          exact ⟨a, Finset.mem_filter.mpr ⟨haS, haTrue⟩⟩
        exact hbT (h ▸ hbNeighborhood)
      · rw [if_neg haS]
        trivial
  · intro h
    ext b
    constructor
    · intro hb
      by_contra hbT
      have hAvoids := h b
      rw [if_neg hbT] at hAvoids
      have hbCount := (Finset.mem_filter.mp hb).2
      have hNonempty :
          (S.filter fun a => sample (a, b)).Nonempty :=
        Finset.card_pos.mp hbCount
      rcases hNonempty with ⟨a, ha⟩
      have haFalse := hAvoids a
      rw [if_pos (Finset.mem_filter.mp ha).1] at haFalse
      have haTrue := (Finset.mem_filter.mp ha).2
      change sample (a, b) = false at haFalse
      rw [haTrue] at haFalse
      contradiction
    · intro hbT
      have hHits := h b
      rw [if_pos hbT] at hHits
      rcases hHits with ⟨a, haS, haTrue⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.card_pos.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨haS, haTrue⟩⟩
end QEC.Coding.FiberBundle.RandomBase

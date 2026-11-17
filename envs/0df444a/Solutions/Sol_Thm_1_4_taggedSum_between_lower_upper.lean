-- Prove2me | solution 1 for Thm_1_4.taggedSum_between_lower_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:44:32.827798+00:00
-- url     : https://prove2.me/submissions/26f951f3-42d8-46b6-818c-bfa50a0a02d3

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_partition_increment_nonneg_of_source_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
open Set DarbouxRS
noncomputable section

theorem solution {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f α ≤ taggedSum P tags f α ∧
      taggedSum P tags f α ≤ upperSum P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold lowerSum taggedSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
      BddBelow.mono
        (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
        hBelow
    have hlow_le_tag : lowerStep P f i ≤ f (tags i) := by
      unfold lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold taggedSum upperSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
      BddAbove.mono
        (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
        hAbove
    have htag_le_up : f (tags i) ≤ upperStep P f i := by
      unfold upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg

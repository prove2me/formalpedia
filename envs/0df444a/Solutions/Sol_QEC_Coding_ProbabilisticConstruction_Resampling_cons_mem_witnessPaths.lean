-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.cons_mem_witnessPaths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:18:35.374113+00:00
-- url     : https://prove2.me/submissions/b57303f7-3bd6-46f3-8816-0b4906c17666

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (h : ℕ) (root j : I) (t : WitnessTree G (h + 1) root)
    (p : List I) :
    j :: p ∈ witnessPaths G (h + 1) root t ↔
      ∃ hj : j ∈ closedNeighbors G root, ∃ child,
        t ⟨j, hj⟩ = some child ∧ p ∈ witnessPaths G h j child := by
  constructor
  · intro hp
    have hm := hp
    simp only [witnessPaths, Finset.mem_insert, List.cons_ne_nil, false_or] at hm



    obtain ⟨k, hk, hm⟩ := Finset.mem_biUnion.mp hm
    cases hc : t k with
    | none => simp [hc] at hm
    | some child =>
      have himg : j :: p ∈ (witnessPaths G h k child).image (List.cons k.val) := by
        simpa [hc] using hm
      obtain ⟨q, hq, he⟩ := Finset.mem_image.mp himg
      have hkj : k.val = j := (List.cons.inj he).1
      have hqp : q = p := (List.cons.inj he).2
      subst j
      subst p
      exact ⟨k.property, child, hc, hq⟩
  · rintro ⟨hj, child, hc, hp⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    rw [hc]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
end QEC.Coding.ProbabilisticConstruction.Resampling

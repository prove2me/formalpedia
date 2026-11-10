-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessWeight_eq_prod_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:24:11.013112+00:00
-- url     : https://prove2.me/submissions/ba4b4a30-aca7-4851-853d-f4ecf6ab3b29

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (p : I → ℝ) (h : ℕ) (i : I)
    (t : WitnessTree G h i) :
    witnessWeight G p h i t = ∏ q ∈ witnessPaths G h i t, p (pathLabel i q) := by
  classical
  induction h generalizing i with
  | zero => exact PEmpty.elim t
  | succ h ih =>
    let children : closedNeighbors G i → Finset (List I) := fun j =>
      match t j with
      | none => ∅
      | some child => (witnessPaths G h j child).image (List.cons j.val)
    have hn : [] ∉ Finset.univ.biUnion children := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
      intro j
      cases hc : t j <;> simp [children, hc]
    have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (closedNeighbors G i))) children := by
      intro j hj k hk hjk
      apply Finset.disjoint_left.mpr
      intro q hqj hqk
      cases hcj : t j with
      | none => simp [children, hcj] at hqj
      | some tj =>
        cases hck : t k with
        | none => simp [children, hck] at hqk
        | some tk =>
          obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (by simpa [children, hcj] using hqj)
          obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp (by simpa [children, hck] using hqk)
          exact hjk (Subtype.ext (List.cons.inj (hea.trans heb.symm)).1)
    change p i * (∏ j, (t j).elim 1 (witnessWeight G p h j)) =
      ∏ q ∈ insert [] (Finset.univ.biUnion children), p (pathLabel i q)
    rw [Finset.prod_insert hn, Finset.prod_biUnion hd]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    cases hc : t j with
    | none => simp [children, hc]
    | some child =>
      simp only [hc, Option.elim_some, children]
      rw [Finset.prod_image]
      · exact ih j child
      · intro a ha b hb he
        exact (List.cons.inj he).2
end QEC.Coding.ProbabilisticConstruction.Resampling

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_le_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:37:08.339192+00:00
-- url     : https://prove2.me/submissions/926f8fcf-0681-4a49-884a-7988fc90befb

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_compatible
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
open scoped Classical
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (T : ℕ) (i : I) :
    prefixCount vars bad R T i ≤
      (Finset.univ.filter (fun t : WitnessTree (supportGraph vars) (T + 1) i =>
        R ∈ compatible vars bad i (witnessPaths (supportGraph vars) (T + 1) i t))).card := by
  classical
  apply Finset.card_le_card_of_injective (f := fun n =>
    ⟨occurrenceTree vars bad R T i n,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, occurrenceTree_compatible vars bad R T i n⟩⟩)
  intro a b he
  exact occurrenceTree_injective vars bad R T i (congrArg Subtype.val he)
end QEC.Coding.ProbabilisticConstruction.Resampling

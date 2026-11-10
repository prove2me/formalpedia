-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witness_address_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:24:32.8712+00:00
-- url     : https://prove2.me/submissions/e8877f8a-573f-4558-bddc-0b22a98841f0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_variableRank_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (P : Finset (List I))
    (hd : DistinctVariableDepth vars root P) :
    Function.Injective (fun s : (p : P) × vars (pathLabel root p.val) =>
      (s.2.val, variableRank vars root P s.1.val s.2.val)) := by
  intro a b he
  have hv : a.2.val = b.2.val := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  have hpb : a.2.val ∈ vars (pathLabel root b.1.val) := hv.symm ▸ b.2.property
  have hp : a.1 = b.1 := Subtype.ext (variableRank_injective vars root P hd
    a.1.val b.1.val a.1.property b.1.property a.2.val a.2.property hpb (by simpa [hv] using hr))
  cases a with
  | mk p v =>
    cases b with
    | mk q w =>
      dsimp only at hp
      subst q
      have hw : v = w := Subtype.ext hv
      subst w
      rfl
end QEC.Coding.ProbabilisticConstruction.Resampling

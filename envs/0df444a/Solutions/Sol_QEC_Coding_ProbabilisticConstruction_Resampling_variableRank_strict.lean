-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:21:08.994023+00:00
-- url     : https://prove2.me/submissions/1f630cfe-aedc-4871-9bb0-98837a121c4b

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (P : Finset (List I))
    (p q : List I) (hq : q ∈ P) (v : V) (hqv : v ∈ vars (pathLabel root q))
    (hdepth : p.length < q.length) :
    variableRank vars root P q v < variableRank vars root P p v := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro r hr
    obtain ⟨hrP, hrv, hqr⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hrP, hrv, lt_trans hdepth hqr⟩
  · intro he
    have hm : q ∈ P.filter (fun r => v ∈ vars (pathLabel root r) ∧ p.length < r.length) :=
      Finset.mem_filter.mpr ⟨hq, hqv, hdepth⟩
    rw [← he] at hm
    exact (Finset.mem_filter.mp hm).2.2.false
end QEC.Coding.ProbabilisticConstruction.Resampling

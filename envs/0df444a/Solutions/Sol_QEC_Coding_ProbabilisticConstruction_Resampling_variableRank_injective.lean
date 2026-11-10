-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:23:00.068423+00:00
-- url     : https://prove2.me/submissions/840ee489-8b2b-4e04-80fb-72f094a0b7d9

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_variableRank_strict

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (P : Finset (List I))
    (hd : DistinctVariableDepth vars root P) (p q : List I) (hp : p ∈ P) (hq : q ∈ P)
    (v : V) (hpv : v ∈ vars (pathLabel root p)) (hqv : v ∈ vars (pathLabel root q))
    (he : variableRank vars root P p v = variableRank vars root P q v) : p = q := by
  apply hd p hp q hq v hpv hqv
  have hle : p.length ≤ q.length := by
    by_contra h
    have hh := variableRank_strict vars root P q p hp v hpv (Nat.lt_of_not_ge h)
    omega
  have hge : q.length ≤ p.length := by
    by_contra h
    have hh := variableRank_strict vars root P p q hq v hqv (Nat.lt_of_not_ge h)
    omega
  exact Nat.le_antisymm hle hge
end QEC.Coding.ProbabilisticConstruction.Resampling

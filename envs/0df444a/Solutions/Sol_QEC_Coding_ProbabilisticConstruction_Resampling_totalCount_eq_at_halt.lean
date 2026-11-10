-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.totalCount_eq_at_halt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:31:29.868346+00:00
-- url     : https://prove2.me/submissions/8a3bba07-a885-4309-8864-2befac5c26d2

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_stable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_monotone


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (n : ℕ)
    (hn : selected vars bad R n = none) (i : I) :
    totalCount vars bad R i = (prefixCount vars bad R n i : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro T
    by_cases hT : T ≤ n
    · exact_mod_cast prefixCount_monotone vars bad R i hT
    · have he := prefixCount_stable vars bad R n hn (T - n) i
      rw [Nat.add_sub_of_le (by omega)] at he
      exact le_of_eq (congrArg (fun k : ℕ => (k : ℝ≥0∞)) he)
  · exact le_iSup (fun T => (prefixCount vars bad R T i : ℝ≥0∞)) n
end QEC.Coding.ProbabilisticConstruction.Resampling

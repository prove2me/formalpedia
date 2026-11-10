-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.halts_of_totalSteps_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:31:27.320268+00:00
-- url     : https://prove2.me/submissions/9a3e29a6-112c-4fd9-b096-a0c01fe7e93e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_sum_prefixCount_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X))
    (hf : totalSteps vars bad R < ∞) : Halts vars bad R := by
  by_contra hn
  have hactive : ∀ n, ∃ i, selected vars bad R n = some i := by
    intro n
    cases he : selected vars bad R n with
    | none => exact False.elim (hn ⟨n, he⟩)
    | some i => exact ⟨i, rfl⟩
  have hl : ∀ T : ℕ, (T : ℝ≥0∞) ≤ totalSteps vars bad R := by
    intro T
    have he := sum_prefixCount_eq vars bad R T (fun n _ => hactive n)
    calc
      (T : ℝ≥0∞) = ∑ i, (prefixCount vars bad R T i : ℝ≥0∞) := by exact_mod_cast he.symm
      _ ≤ totalSteps vars bad R := Finset.sum_le_sum (fun i _ => le_iSup
        (fun N => (prefixCount vars bad R N i : ℝ≥0∞)) T)
  have htop : ∞ ≤ totalSteps vars bad R := by
    rw [← ENNReal.iSup_natCast]
    exact iSup_le hl
  exact hf.not_ge htop
end QEC.Coding.ProbabilisticConstruction.Resampling

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:18.708196+00:00
-- url     : https://prove2.me/submissions/ca2561e0-0174-4a8a-bce1-d2e88c6f8cde

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution [LinearOrder I] {L : List I} (hL : L.Pairwise (· ≤ ·))
    {ω : Ω} {i : I} (hi : firstBadFrom B L ω = some i)
    {j : I} (hj : j ∈ L) (hbad : ω ∈ B j) : i ≤ j := by
  induction L with
  | nil => simp at hj
  | cons k L ih =>
    obtain ⟨hkL, hLL⟩ := List.pairwise_cons.mp hL
    by_cases hk : ω ∈ B k
    · have he : k = i := by simpa [firstBadFrom, hk] using hi
      subst k
      rcases List.mem_cons.mp hj with he | hj
      · exact le_of_eq he.symm
      · exact hkL j hj
    · have hi' : firstBadFrom B L ω = some i := by simpa [firstBadFrom, hk] using hi
      rcases List.mem_cons.mp hj with he | hj
      · exact False.elim (hk (he ▸ hbad))
      · exact ih hLL hi' hj
end QEC.Coding.ProbabilisticConstruction.Resampling

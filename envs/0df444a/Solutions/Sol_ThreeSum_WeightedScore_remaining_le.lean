-- Prove2me | solution 1 for ThreeSum.WeightedScore.remaining_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:56:04.810609+00:00
-- url     : https://prove2.me/submissions/7b1fda17-b26a-4808-841b-a42f6b9325ef

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c i ≤ s * (nA*nB*nC) :=
  (Nat.sub_le _ _).trans (Nat.mul_le_mul_left s (count_le q nA nB nC a b c))
end ThreeSum.WeightedScore

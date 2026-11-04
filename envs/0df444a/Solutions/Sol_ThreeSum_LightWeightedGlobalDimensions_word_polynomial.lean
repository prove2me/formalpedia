-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalDimensions.word_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:27:51.481444+00:00
-- url     : https://prove2.me/submissions/3e883822-ea69-482e-8df4-e3a8756b21e7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_word_linear_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeSum.LightWeightedGlobalDimensions
theorem _root_.solution {M b p K : ℕ} [Fact p.Prime]
    (hM : 1<M) (hb : 1<b) (n U : ℕ) :
    word M b p K n U≤coefficient M b p K*(n+1)^2*(U+1) := by
  have hN : n^2≤(n+1)^2 := by gcongr; omega
  have hNmul : (n+1)^2≤(n+1)^2*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hUmul : U+1≤(n+1)^2*(U+1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hD : n^2+4*U+3≤5*((n+1)^2*(U+1)) := by omega
  apply (word_linear_bound hM hb n U).trans
  unfold coefficient
  nlinarith [Nat.mul_le_mul_left (1000*(coefficientBase M b p K)^2) hD]
end ThreeSum.LightWeightedGlobalDimensions

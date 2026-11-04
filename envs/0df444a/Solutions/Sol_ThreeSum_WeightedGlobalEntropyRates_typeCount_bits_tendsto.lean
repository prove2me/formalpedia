-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.typeCount_bits_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:37.38228+00:00
-- url     : https://prove2.me/submissions/3f747794-33e7-4be4-8cb7-4b734e1ee2e7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bits_tendsto


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution {N r1 r2 : ℕ} (hN : 0 < N)
    (h2 : r2 < N) (h1 : r1+r2 ≤ N) :
    Tendsto (fun m : ℕ => Real.log (typeCount N r1 r2 m : ℝ)/
      (((N*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 (splitBits N r1 r2)) := by
  have hfirst := BinomialEntropy.fixed_ratio_bits_tendsto hN h2.le
  have hrest := BinomialEntropy.fixed_ratio_bits_tendsto (Nat.sub_pos_of_lt h2)
    (show r1 ≤ N-r2 by omega)
  have h := (hfirst.add hrest).div_const (N : ℝ)
  convert h using 1
  · funext m
    unfold typeCount
    rw [Nat.cast_mul, Real.log_mul]
    · push_cast
      ring
    · exact_mod_cast (Nat.choose_pos (Nat.mul_le_mul_right m h2.le)).ne'
    · exact_mod_cast (Nat.choose_pos (Nat.mul_le_mul_right m (show r1 ≤ N-r2 by omega))).ne'
  · rfl
end ThreeSum.WeightedGlobalEntropyRates

-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.typeCount_bits_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:33.667197+00:00
-- url     : https://prove2.me/submissions/127c80e2-22ad-47fb-81e5-3a0d8f0b6a87

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bits_tendsto


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
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
end ThreeSum.TernaryEntropyRates

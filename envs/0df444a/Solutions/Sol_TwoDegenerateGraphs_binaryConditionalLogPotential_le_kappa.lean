-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryConditionalLogPotential_le_kappa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/2e780d7d-bfdb-4154-9c58-545c4d333731

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binary_pinsker
import Theorems.Thm_TwoDegenerateGraphs_log_four_thirds_lt_one_third
import Theorems.Thm_TwoDegenerateGraphs_sqrt_one_add_le
import Theorems.Thm_TwoDegenerateGraphs_binaryConditionalLogPotential_tangent_bound

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      kappa * Real.log 2 := by
  have htangent := binaryConditionalLogPotential_tangent_bound
    q zeroAmplitude oneAmplitude hqzero hqone
    hzeroAmplitude honeAmplitude hamplitudes
  have hpinsker := binary_pinsker q hqzero hqone
  have hsqrt := sqrt_one_add_le ((2 * q - 1) ^ 2 / 4)
    (by positivity)
  have hlogscaled := mul_le_mul_of_nonneg_left
    log_four_thirds_lt_one_third.le
    (show 0 ≤ (2 * q - 1) ^ 2 / 4 by positivity)
  have hkappa :
      kappa * Real.log 2 =
        (3 / 2 : ℝ) * Real.log 2 -
          (3 / 4 : ℝ) * Real.log 3 := by
    unfold kappa logTwo
    field_simp [log_two_pos.ne']
  rw [hkappa]
  nlinarith [sq_nonneg (2 * q - 1)]
end TwoDegenerateGraphs

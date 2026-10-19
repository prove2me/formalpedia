-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryConditionalLogPotential_tangent_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/6fd6248c-77b6-48da-81fe-8c1151814001

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_log_le_tangent
import Theorems.Thm_TwoDegenerateGraphs_normalized_binary_cauchy
import Theorems.Thm_TwoDegenerateGraphs_entropyTangentSigma_pos
import Theorems.Thm_TwoDegenerateGraphs_entropyTangentRho_pos
import Theorems.Thm_TwoDegenerateGraphs_entropyTangentZeroCoefficient_eq
import Theorems.Thm_TwoDegenerateGraphs_entropyTangentOneCoefficient_eq
import Theorems.Thm_TwoDegenerateGraphs_entropyTangentCoefficient_norm
import Theorems.Thm_TwoDegenerateGraphs_entropyTangentLog_constant

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
      Real.binEntropy q / 2 +
        Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) +
        Real.sqrt (1 + (2 * q - 1) ^ 2 / 4) - 1 := by
  have hsum : 0 < zeroAmplitude + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargzero : 0 < zeroAmplitude + oneAmplitude / 3 := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargone : 0 < zeroAmplitude / 3 + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hargmixed :
      0 < (zeroAmplitude + oneAmplitude) / Real.sqrt 3 :=
    div_pos hsum hthree
  have htangentzero := mul_le_mul_of_nonneg_left
    (log_le_tangent hargzero entropyTangentSigma_pos)
    (sq_nonneg (1 - q))
  have htangentone := mul_le_mul_of_nonneg_left
    (log_le_tangent hargone entropyTangentSigma_pos)
    (sq_nonneg q)
  have hmixedweight : 0 ≤ 2 * q * (1 - q) := by
    have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
    positivity
  have htangentmixed := mul_le_mul_of_nonneg_left
    (log_le_tangent hargmixed entropyTangentRho_pos)
    hmixedweight
  have hcombined :=
    add_le_add (add_le_add htangentzero htangentone) htangentmixed
  have hright :
      ((1 - q) ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude + oneAmplitude / 3) /
              entropyTangentSigma - 1) +
        q ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude / 3 + oneAmplitude) /
              entropyTangentSigma - 1)) +
        (2 * q * (1 - q)) *
          (Real.log entropyTangentRho +
            ((zeroAmplitude + oneAmplitude) / Real.sqrt 3) /
              entropyTangentRho - 1) =
        ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
          2 * q * (1 - q) * Real.log entropyTangentRho +
          zeroAmplitude * entropyTangentZeroCoefficient q +
          oneAmplitude * entropyTangentOneCoefficient q - 1 := by
    rw [← entropyTangentZeroCoefficient_eq,
      ← entropyTangentOneCoefficient_eq]
    field_simp [entropyTangentSigma_pos.ne',
      entropyTangentRho_pos.ne', hthree.ne']
    ring
  rw [hright, entropyTangentLog_constant] at hcombined
  have hcauchy := normalized_binary_cauchy
    zeroAmplitude oneAmplitude
    (entropyTangentZeroCoefficient q)
    (entropyTangentOneCoefficient q) hamplitudes
  rw [entropyTangentCoefficient_norm] at hcauchy
  unfold binaryConditionalLogPotential
  linarith
end TwoDegenerateGraphs

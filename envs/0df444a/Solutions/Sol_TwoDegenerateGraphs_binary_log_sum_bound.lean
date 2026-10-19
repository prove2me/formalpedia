-- Prove2me | solution 1 for TwoDegenerateGraphs.binary_log_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/30f04be2-621c-4024-bb96-afe94d744926

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (probability zeroWeight oneWeight : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hzeroWeight : 0 < zeroWeight)
    (honeWeight : 0 < oneWeight) :
    Real.binEntropy probability +
        (1 - probability) * Real.log zeroWeight +
        probability * Real.log oneWeight ≤
      Real.log (zeroWeight + oneWeight) := by
  by_cases hzero : probability = 0
  · subst probability
    simpa using Real.log_le_log hzeroWeight
      (le_add_of_nonneg_right honeWeight.le)
  by_cases hone : probability = 1
  · subst probability
    simpa using Real.log_le_log honeWeight
      (le_add_of_nonneg_left hzeroWeight.le)
  have hprobability_pos : 0 < probability :=
    lt_of_le_of_ne hprobability_zero (Ne.symm hzero)
  have hcomplement_pos : 0 < 1 - probability :=
    sub_pos.mpr (lt_of_le_of_ne hprobability_one hone)
  have hnormalize :
      (1 - probability) * (zeroWeight / (1 - probability)) +
          probability * (oneWeight / probability) =
        zeroWeight + oneWeight := by
    field_simp [hprobability_pos.ne', hcomplement_pos.ne']
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.2
    (show zeroWeight / (1 - probability) ∈ Set.Ioi (0 : ℝ) from
      div_pos hzeroWeight hcomplement_pos)
    (show oneWeight / probability ∈ Set.Ioi (0 : ℝ) from
      div_pos honeWeight hprobability_pos)
    hcomplement_pos.le hprobability_pos.le
    (show (1 - probability) + probability = 1 by ring)
  simp only [smul_eq_mul] at hjensen
  rw [hnormalize] at hjensen
  rw [Real.log_div hzeroWeight.ne' hcomplement_pos.ne',
    Real.log_div honeWeight.ne' hprobability_pos.ne'] at hjensen
  have hentropy :
      Real.binEntropy probability =
        -(1 - probability) * Real.log (1 - probability) -
          probability * Real.log probability := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  rw [hentropy]
  linarith
end TwoDegenerateGraphs

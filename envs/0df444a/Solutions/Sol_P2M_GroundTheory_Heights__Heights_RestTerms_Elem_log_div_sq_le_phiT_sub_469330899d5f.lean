-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:48.411785+00:00
-- url     : https://prove2.me/submissions/563fb11c-cb96-4777-a9f8-4447ea258414

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution (x : ℝ) (hx : 3 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ phiT x - phiT (x + 1) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log (x + 1)
  set l := Real.log x
  have hlL : L - 1 / x ≤ l := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hL : 1 + 1 / x ≤ L := by
    have h2 := Real.log_two_gt_d9
    have h4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h13 : 1 / x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hx
    linarith
  have hmain : (1 + (L - 1 / x)) / x - (1 + L) / (x + 1) - L / (x + 1) ^ 2 =
      (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  have hnum : 0 ≤ L * x - x - 1 := by
    have : (1 + 1 / x) * x = x + 1 := by field_simp
    nlinarith
  have h1 : (1 + (L - 1 / x)) / x ≤ (1 + l) / x :=
    div_le_div_of_nonneg_right (by linarith) hx0.le
  have h2 : 0 ≤ (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by positivity
  unfold phiT
  linarith
end GroundTheory.Heights₂.Heights.RestTerms.Elem

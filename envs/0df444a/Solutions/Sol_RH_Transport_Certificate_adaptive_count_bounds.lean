-- Prove2me | solution 1 for RH.Transport.Certificate.adaptive_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:29.623856+00:00
-- url     : https://prove2.me/submissions/d8840499-e670-44f3-973c-7392f8d01093

import Definitions.Def_Transport_Candidate
import Definitions.Def_Transport_Endpoint
import Definitions.Def_Transport_Certificate
import Theorems.Thm_RH_Transport_Endpoint_countDenominator_pos


set_option autoImplicit false
open RH RH.Transport RH.Transport.Certificate
noncomputable section
namespace RH.Transport.Certificate
theorem _root_.solution {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    1 - δ ≤ Endpoint.adaptiveCount δ x ∧ Endpoint.adaptiveCount δ x ≤ 1 := by
  have hJ := Endpoint.countDenominator_pos hdlo hdhi hxlo hxhi
  have hd : 0 ≤ δ := by linarith
  have ha : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hP : 0 ≤ ((2 : ℝ) - 8 * x / 9) * (1 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hP2 : ((2 : ℝ) - 8 * x / 9) * (1 - x) ≤ 2 := by
    calc
      _ ≤ 2 * (1 - x) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 2 := by linarith
  have hD : (2 : ℝ) ≤ 3 - 17 * x / 9 := by linarith
  have hPD : ((2 : ℝ) - 8 * x / 9) * (1 - x) ≤ 3 - 17 * x / 9 :=
    hP2.trans hD
  have hPJ : (5 / 6 - δ) * ((2 - 8 * x / 9) * (1 - x)) ≤
      Endpoint.countDenominator δ x := by
    have hm := mul_le_mul_of_nonneg_left hPD ha
    have hn := mul_nonneg hd hP
    unfold Endpoint.countDenominator
    linarith
  have hnum : 0 ≤ (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) :=
    mul_nonneg (mul_nonneg ha hd) hP
  have hquot0 := div_nonneg hnum (show 0 ≤ 2 * Endpoint.countDenominator δ x by positivity)
  have hquot : (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) /
      (2 * Endpoint.countDenominator δ x) ≤ δ := by
    apply (div_le_iff₀ (show 0 < 2 * Endpoint.countDenominator δ x by positivity)).2
    have hm := mul_le_mul_of_nonneg_left hPJ hd
    have hn := mul_nonneg hd hJ.le
    nlinarith
  unfold Endpoint.adaptiveCount
  constructor <;> linarith
end RH.Transport.Certificate

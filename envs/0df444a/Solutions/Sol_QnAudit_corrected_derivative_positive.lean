-- Prove2me | solution 1 for QnAudit.corrected_derivative_positive
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:23.727628+00:00
-- url     : https://prove2.me/submissions/52eb2b44-7979-4e25-991d-d653c7a987ec

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_log_factor_ge_one
open MeasureTheory Set
open QnAudit

theorem solution (k c t : ℝ)
    (ht : 0 < t) (hsmall : t ≤ 1/2) (hc : 0 ≤ c) (hk : 3*t < k) :
    0 < k / t ^ 2 + c + 1/4 - 1/t -
        2 / (t * (2*t^2+1) * Real.log (2+1/t^2)) := by
  have hL := log_factor_ge_one t ht hsmall
  have hfac : 1 ≤ 2*t^2+1 := by nlinarith [sq_nonneg t]
  have hprod : 1 ≤ (2*t^2+1) * Real.log (2+1/t^2) := by nlinarith
  have hden : t ≤ t * (2*t^2+1) * Real.log (2+1/t^2) := by nlinarith
  have hfrac : 2 / (t * (2*t^2+1) * Real.log (2+1/t^2)) ≤ 2/t :=
    div_le_div_of_nonneg_left (by norm_num) ht hden
  have hkdiv : 3/t < k / t^2 := by
    apply (div_lt_div_iff₀ ht (pow_pos ht 2)).2
    nlinarith
  have hthree : 3/t = 1/t + 2/t := by ring
  linarith

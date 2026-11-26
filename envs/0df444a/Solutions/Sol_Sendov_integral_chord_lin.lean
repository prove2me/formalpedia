-- Prove2me | solution 1 for Sendov.integral_chord_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:46.473547+00:00
-- url     : https://prove2.me/submissions/24290185-7fcf-41bf-9372-8a5a18c1a321

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_integral_lin_mul_rpow

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t * (1 - c * t) ^ s) = 1 / (c ^ 2 * ((s + 1) * (s + 2))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) * (1 - y) ^ s) hc'
  have hfun : (fun t : ℝ => ((c * t) / c) * (1 - c * t) ^ s)
      = fun t : ℝ => t * (1 - c * t) ^ s := by
    funext t
    rw [mul_div_cancel_left₀ t hc']
  simp only [hfun] at h
  rw [show c * (1 / c) = 1 by field_simp, mul_zero] at h
  have hg : (fun y : ℝ => (y / c) * (1 - y) ^ s)
      = fun y : ℝ => (1 / c) * (y * (1 - y) ^ s) := by
    funext y
    field_simp
  rw [hg, intervalIntegral.integral_const_mul, integral_lin_mul_rpow hs] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp
end Sendov

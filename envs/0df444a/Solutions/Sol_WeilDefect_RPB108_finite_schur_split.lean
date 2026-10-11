-- Prove2me | solution 1 for WeilDefect.RPB108.finite_schur_split
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:28:28.134072+00:00
-- url     : https://prove2.me/submissions/8d85c7fd-1651-40a6-88ae-b2965568cd8e

import Theorems.Thm_WeilDefect_RPB108_inverse_covariance_split
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r v : E) (z p : ℂ)
    (N lowDiag retainedNative : ℝ)
    (hherm : inner ℂ v (T r) = star (inner ℂ r (T v)))
    (hnative : N = lowDiag*‖z‖^2+2*(star z*p).re+retainedNative) :
    N-(inner ℂ (z • r+v) (T (z • r+v))).re =
      (lowDiag-(inner ℂ r (T r)).re)*‖z‖^2+
      2*(star z*(p-inner ℂ r (T v))).re+
      (retainedNative-(inner ℂ v (T v)).re) := by
  rw [inverse_covariance_split T r v z hherm, hnative]
  simp only [mul_sub, Complex.sub_re]
  ring

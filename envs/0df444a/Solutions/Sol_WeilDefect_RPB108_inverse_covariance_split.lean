-- Prove2me | solution 1 for WeilDefect.RPB108.inverse_covariance_split
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:25:53.190929+00:00
-- url     : https://prove2.me/submissions/7d9ad0de-f71c-4bcb-99ea-93b2683eff43

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r v : E) (z : ℂ)
    (hherm : inner ℂ v (T r) = star (inner ℂ r (T v))) :
    (inner ℂ (z • r+v) (T (z • r+v))).re =
      ‖z‖^2*(inner ℂ r (T r)).re+
      2*(star z*inner ℂ r (T v)).re+(inner ℂ v (T v)).re := by
  have hz : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hherm]
  rw [hz]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

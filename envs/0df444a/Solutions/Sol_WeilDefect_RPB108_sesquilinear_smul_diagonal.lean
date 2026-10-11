-- Prove2me | solution 1 for WeilDefect.RPB108.sesquilinear_smul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:25:59.855979+00:00
-- url     : https://prove2.me/submissions/eb8c9b8a-5db9-41e7-9fc0-e6c19046f454

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ) (z : ℂ) (u : E) :
    (F (z • u) (z • u)).re = ‖z‖^2*(F u u).re := by
  have hz : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul]
  rw [hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

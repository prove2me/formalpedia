-- Prove2me | solution 1 for WeilDefect.RPB108.sesquilinear_gram
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:27:48.53472+00:00
-- url     : https://prove2.me/submissions/7e51f719-87e8-45e7-bb7b-7c67e804f603

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ) (x : Fin 3 → E)
    (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ i j, F (x i) (x j) = (M i j : ℂ))
    (z : Fin 3 → ℂ) :
    (F (∑ i, z i • x i) (∑ i, z i • x i)).re = complexGram M z := by
  rw [LinearMap.map_sum₂]
  simp only [map_sum, LinearMap.map_smulₛₗ₂,
    map_smul, smul_eq_mul, hM, Complex.re_sum, complexGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

-- Prove2me | solution 1 for WeilDefect.RPB108.source_gram_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:27:40.543473+00:00
-- url     : https://prove2.me/submissions/f63f1aa9-7fa8-4ab6-be9f-c613d9cac5f2

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (r : Fin 3 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hG : ∀ i j, inner ℂ (r i) (r j) = (G i j : ℂ)) (z : Fin 3 → ℂ) :
    ‖∑ i, z i • r i‖^2 = complexGram G z := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ (∑ i, z i • r i) (∑ i, z i • r i)).re = _
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, hG,
    Complex.re_sum, complexGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]
  ring

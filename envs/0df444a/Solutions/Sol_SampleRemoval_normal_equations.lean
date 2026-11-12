-- Prove2me | solution 1 for SampleRemoval.normal_equations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:45.236592+00:00
-- url     : https://prove2.me/submissions/5a014a2d-d1cc-406f-a72a-b163a7c00786

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_ols

section
set_option autoImplicit false

open Matrix

namespace SampleRemoval
namespace Dev
namespace NormalEq

theorem residual_sum {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (b : Fin d → ℝ) :
    ∑ i, (w i * (y i - x i ⬝ᵥ b)) • x i = moment x y w - gram x w *ᵥ b := by
  ext j
  simp only [moment, gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm (f := fun k c => w c * (x c j * x c k) * b k), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem iff_aux {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (hG : (gram x w).PosDef) (b : Fin d → ℝ) :
    ∑ i, (w i * (y i - x i ⬝ᵥ b)) • x i = 0 ↔ b = ols x y w := by
  have hdet : IsUnit (gram x w).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  rw [residual_sum, sub_eq_zero]
  constructor
  · intro h
    rw [ols, h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · intro h
    rw [h, ols, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

end NormalEq
end Dev

theorem chk_normal_equations {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (hG : (gram x w).PosDef) (b : Fin d → ℝ) :
    ∑ i, (w i * (y i - x i ⬝ᵥ b)) • x i = 0 ↔ b = ols x y w :=
  Dev.NormalEq.iff_aux x y w hG b

end SampleRemoval

end

theorem solution : type_of% @SampleRemoval.chk_normal_equations := @SampleRemoval.chk_normal_equations

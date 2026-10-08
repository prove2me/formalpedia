-- Prove2me | solution 1 for PeresTerno.krausUpdate_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:09:14.920029+00:00
-- url     : https://prove2.me/submissions/57a7ac4d-f430-4758-91b8-ac5ae91477e7

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

/-- The ampliated Kraus operator `A ⊗ 1_n`. -/
noncomputable def PeresTerno_krausAmp {d e : Type*} (M : Matrix e d ℂ) (n : ℕ) :
    Matrix (e × Fin n) (d × Fin n) ℂ :=
  Matrix.of fun p x => if p.2 = x.2 then M p.1 x.1 else 0

open PeresTerno in
theorem PeresTerno_ampliate_kraus_eq {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) (n : ℕ) (R : Matrix (d × Fin n) (d × Fin n) ℂ) :
    ampliate (krausUpdate A) R =
      ∑ m, PeresTerno_krausAmp (A m) n * R * (PeresTerno_krausAmp (A m) n)ᴴ := by
  ext p q
  simp only [ampliate, krausUpdate, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, PeresTerno_krausAmp, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, apply_ite star, star_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  change (∑ y, A m p.1 y * R (y, p.2) (x, q.2)) * _ = _
  rw [Finset.sum_mul]

open PeresTerno in
theorem solution {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) :
    IsCompletelyPositive (krausUpdate A) := by
  intro n R hR
  rw [PeresTerno_ampliate_kraus_eq]
  exact Matrix.posSemidef_sum _ fun m _ => hR.mul_mul_conjTranspose_same _

-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.det_gram_eq_prod_gramSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:32.511405+00:00
-- url     : https://prove2.me/submissions/662bd80e-e2f2-4540-acc9-039bd989d094

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetGramEqProdGramSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open Finset InnerProductSpace
private theorem exists_eq_gramSchmidt_add_sum_Iio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n : ℕ) (v : Fin n → E) :
    ∃ c : Fin n → Fin n → ℂ,
      ∀ j, v j = gramSchmidt ℂ v j + ∑ i ∈ Iio j, c j i • gramSchmidt ℂ v i :=
  ⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset InnerProductSpace
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else if i < j then c j i else 0
  have hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i := by
    intro j
    have h1 : ∀ i, A i j • gramSchmidt ℂ v i =
        (if i = j then gramSchmidt ℂ v i else 0) +
          (if i < j then c j i • gramSchmidt ℂ v i else 0) := by
      intro i
      by_cases h : i = j
      · subst h; simp [A]
      · by_cases h' : i < j
        · simp [A, h, h']
        · simp [A, h, h']
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, hc j]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp
  have horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ =
      if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [if_neg h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]
  have hG : Matrix.gram ℂ v =
      Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A := by
    ext i j
    show ⟪v i, v j⟫_ℂ = _
    rw [hA i, hA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero,
      Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
      Matrix.conjTranspose_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hAtri : A.BlockTriangular id := by
    intro i j h
    simp only [id] at h
    simp [A, h.ne', not_lt.mpr h.le]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAtri]
    simp [A]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]
  simp
end ReciprocityTheory.MultiplicativeHeights

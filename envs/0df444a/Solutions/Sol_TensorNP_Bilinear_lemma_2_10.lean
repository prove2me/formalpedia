-- Prove2me | solution 1 for TensorNP.Bilinear.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:38:35.996701+00:00
-- url     : https://prove2.me/submissions/77defeaa-82de-4e53-8ac4-24f312632470

import Mathlib
import Definitions.Def_TensorNP_Bilinear_ColorEncoding
import Definitions.Def_TensorNP_Eigen_Construction
import Theorems.Thm_TensorNP_Eigen_lemma_2_10

open Matrix Finset

private lemma dotProduct_single_one_mulVec {n : ℕ} (a b : Fin n) (p : Fin n → ℂ) :
    p ⬝ᵥ (Matrix.single a b (1 : ℂ) *ᵥ p) = p a * p b := by
  simp [dotProduct, Matrix.mulVec, Matrix.single]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj.symm]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · intro i _ hi; simp [hi.symm]
  · intro ha; exact absurd (Finset.mem_univ a) ha

private lemma map_sub_ratCast {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A - B).map (Rat.cast : ℚ → ℂ) = A.map (Rat.cast : ℚ → ℂ) - B.map (Rat.cast : ℚ → ℂ) := by
  ext i j; simp

private lemma map_add_ratCast {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A + B).map (Rat.cast : ℚ → ℂ) = A.map (Rat.cast : ℚ → ℂ) + B.map (Rat.cast : ℚ → ℂ) := by
  ext i j; simp

private lemma map_sum_ratCast {v n : ℕ} (s : Finset (Fin v)) (f : Fin v → Matrix (Fin n) (Fin n) ℚ) :
    (∑ j ∈ s, f j).map (Rat.cast : ℚ → ℂ) = ∑ j ∈ s, (f j).map (Rat.cast : ℚ → ℂ) := by
  ext a b; simp [Matrix.sum_apply, Rat.cast_sum]

private lemma map_single_one_ratCast {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : ℚ)).map (Rat.cast : ℚ → ℂ) = Matrix.single a b (1 : ℂ) := by
  ext i j; simp [Matrix.single]; split_ifs <;> simp

private lemma eigen_quad_eq_bilin {v : ℕ} (G : SimpleGraph (Fin v)) (c : Fin 4) (i : Fin v)
    (p : Fin (2 * v + 1) → ℂ) :
    p ⬝ᵥ (TensorNP.Eigen.castMatrices ℂ (TensorNP.Eigen.colorEncoding G) (c, i) *ᵥ p) =
      TensorNP.Bilinear.colorEncoding G c i p := by
  classical
  rcases c with ⟨c_val, hc⟩
  interval_cases c_val
  · simp only [TensorNP.Eigen.castMatrices, TensorNP.Eigen.colorEncoding,
      TensorNP.Bilinear.colorEncoding, Fin.zero_eta, Matrix.cons_val_zero,
      map_sub_ratCast, map_single_one_ratCast, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_single_one_mulVec, sq, TensorNP.Eigen.xVar, TensorNP.Eigen.yVar,
      TensorNP.Eigen.zVar, TensorNP.Bilinear.xIdx, TensorNP.Bilinear.yIdx, TensorNP.Bilinear.zIdx]
  · simp only [TensorNP.Eigen.castMatrices, TensorNP.Eigen.colorEncoding,
      TensorNP.Bilinear.colorEncoding, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      map_sub_ratCast, map_single_one_ratCast, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_single_one_mulVec, sq, TensorNP.Eigen.xVar, TensorNP.Eigen.yVar,
      TensorNP.Eigen.zVar, TensorNP.Bilinear.xIdx, TensorNP.Bilinear.yIdx, TensorNP.Bilinear.zIdx]
  · have hc2 : TensorNP.Eigen.colorEncoding G (⟨2, hc⟩, i) =
        single (TensorNP.Eigen.xVar i) TensorNP.Eigen.zVar 1 -
          single (TensorNP.Eigen.yVar i) (TensorNP.Eigen.yVar i) 1 := rfl
    simp only [TensorNP.Eigen.castMatrices, hc2, TensorNP.Bilinear.colorEncoding,
      map_sub_ratCast, map_single_one_ratCast, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_single_one_mulVec, sq, TensorNP.Eigen.xVar, TensorNP.Eigen.yVar,
      TensorNP.Eigen.zVar, TensorNP.Bilinear.xIdx, TensorNP.Bilinear.yIdx, TensorNP.Bilinear.zIdx]
  · have hc3 : TensorNP.Eigen.colorEncoding G (⟨3, hc⟩, i) =
        ∑ j ∈ univ.filter (G.Adj i),
          (single (TensorNP.Eigen.xVar i) (TensorNP.Eigen.xVar i) 1 +
            single (TensorNP.Eigen.xVar i) (TensorNP.Eigen.xVar j) 1 +
            single (TensorNP.Eigen.xVar j) (TensorNP.Eigen.xVar j) 1) := rfl
    simp only [TensorNP.Eigen.castMatrices, hc3, TensorNP.Bilinear.colorEncoding, map_sum_ratCast]
    have hsum : ∀ (s : Finset (Fin v)) (f : Fin v → Matrix (Fin (2 * v + 1)) (Fin (2 * v + 1)) ℂ),
        p ⬝ᵥ ((∑ j ∈ s, f j) *ᵥ p) = ∑ j ∈ s, p ⬝ᵥ (f j *ᵥ p) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [Finset.sum_insert ha, Matrix.add_mulVec, dotProduct_add, ih]
    rw [hsum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [map_add_ratCast, map_add_ratCast, map_single_one_ratCast, map_single_one_ratCast,
          map_single_one_ratCast, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add,
          dotProduct_add, dotProduct_single_one_mulVec, dotProduct_single_one_mulVec,
          dotProduct_single_one_mulVec]
      simp only [sq, TensorNP.Eigen.xVar, TensorNP.Bilinear.xIdx]
    · rfl

theorem solution {v : ℕ} (G : SimpleGraph (Fin v)) :
    (∃ p : Fin (2 * v + 1) → ℂ, p ≠ 0 ∧ ∀ (c : Fin 4) (i : Fin v),
        TensorNP.Bilinear.colorEncoding G c i p = 0) ↔
      G.Colorable 3 := by
  rw [← TensorNP.Eigen.lemma_2_10 G]
  unfold TensorNP.Eigen.QuadSolvable
  simp [Prod.forall, eigen_quad_eq_bilin]

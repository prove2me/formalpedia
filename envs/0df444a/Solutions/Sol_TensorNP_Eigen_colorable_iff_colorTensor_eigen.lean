-- Prove2me | solution 1 for TensorNP.Eigen.colorable_iff_colorTensor_eigen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:36:05.184676+00:00
-- url     : https://prove2.me/submissions/db52e434-eb09-42dd-9365-2b0e0ec7078f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TensorNP_Eigen_Construction
import Theorems.Thm_TensorNP_Eigen_eigen_zero_iff_square_feasible
import Theorems.Thm_TensorNP_Eigen_lemma_2_8
import Theorems.Thm_TensorNP_Eigen_lemma_2_7
import Theorems.Thm_TensorNP_Eigen_lemma_2_10

open TensorNP.Eigen Matrix

private lemma castMatrices_padSystem {m n r s : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ) :
    castMatrices ℝ (padSystem A r s) = padSystem (castMatrices ℝ A) r s := by
  ext k a b
  simp only [castMatrices, Matrix.map_apply, padSystem]
  split_ifs <;> simp

private lemma quadSolvable_colorEncodingFin_iff {v : ℕ} (G : SimpleGraph (Fin v)) :
    QuadSolvable (castMatrices ℂ (colorEncodingFin G)) ↔
      QuadSolvable (castMatrices ℂ (colorEncoding G)) := by
  unfold QuadSolvable colorEncodingFin castMatrices
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun ci => ?_⟩
    simpa using h (finProdFinEquiv ci)
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun k => h (finProdFinEquiv.symm k)⟩

theorem solution {v : ℕ} (G : SimpleGraph (Fin v)) :
    G.Colorable 3 ↔ IsEigenvalue (castTensor ℝ (colorTensor G)) 0 := by
  rw [eigen_zero_iff_square_feasible]
  have hsq : (fun k : Fin (colorSize v) => Matrix.of fun i j => colorTensor G i j k) =
      squareSystem G := by
    ext k i j
    rfl
  rw [hsq]
  unfold squareSystem
  rw [castMatrices_padSystem]
  have hr : 4 * v + 4 * v + 1 ≤ colorSize v := by unfold colorSize; omega
  have hs : (2 * v + 1) + (2 * v + 1) ≤ colorSize v := by unfold colorSize; omega
  rw [lemma_2_8 (castMatrices ℝ (realSplit (colorEncodingFin G))) hr hs]
  rw [lemma_2_7 (colorEncodingFin G)]
  rw [quadSolvable_colorEncodingFin_iff G]
  exact (lemma_2_10 G).symm

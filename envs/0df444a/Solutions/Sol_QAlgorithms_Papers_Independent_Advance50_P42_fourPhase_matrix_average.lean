-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P42.fourPhase_matrix_average
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:16:59.836956+00:00
-- url     : https://prove2.me/submissions/aabcfe3f-0d49-4797-b450-1788117309c5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P42
noncomputable section

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Advance50.P42

theorem solution
    (sigma : Matrix (Fin 4) (Fin 4) ℝ) (hsigma : sigma.IsSymm) :
    let a := (sigma 0 0 + sigma 1 1) / 2
    let b := (sigma 2 2 + sigma 3 3) / 2
    let c1 := (sigma 0 3 + sigma 1 2) / 2
    let c2 := (sigma 0 2 - sigma 1 3) / 2
    let z := Real.sqrt (c1 ^ 2 + c2 ^ 2)
    fourPhaseAverage sigma = (1 / 2 : ℝ) •
      !![sigma 0 0 + sigma 1 1, 0, sigma 0 2 - sigma 1 3, sigma 0 3 + sigma 1 2;
         0, sigma 0 0 + sigma 1 1, sigma 0 3 + sigma 1 2, -(sigma 0 2 - sigma 1 3);
         sigma 0 2 - sigma 1 3, sigma 0 3 + sigma 1 2, sigma 2 2 + sigma 3 3, 0;
         sigma 0 3 + sigma 1 2, -(sigma 0 2 - sigma 1 3), 0, sigma 2 2 + sigma 3 3] ∧
    fourPhaseAverage sigma = phaseSymmetricMatrix a b c1 c2 ∧
    ∃ theta : ℝ, c1 = z * Real.sin theta ∧ c2 = z * Real.cos theta ∧
      fourPhaseAverage sigma =
        phaseSymmetricMatrix a b (z * Real.sin theta) (z * Real.cos theta) := by
  intro a b c1 c2 z
  have hs : ∀ i j, sigma i j = sigma j i := fun i j => (hsigma.apply i j).symm
  have hmain : fourPhaseAverage sigma = (1 / 2 : ℝ) •
      !![sigma 0 0 + sigma 1 1, 0, sigma 0 2 - sigma 1 3, sigma 0 3 + sigma 1 2;
         0, sigma 0 0 + sigma 1 1, sigma 0 3 + sigma 1 2, -(sigma 0 2 - sigma 1 3);
         sigma 0 2 - sigma 1 3, sigma 0 3 + sigma 1 2, sigma 2 2 + sigma 3 3, 0;
         sigma 0 3 + sigma 1 2, -(sigma 0 2 - sigma 1 3), 0, sigma 2 2 + sigma 3 3] := by
    have e0 : Real.pi * ((0 : Fin 4).val : ℝ) / 2 = 0 := by simp
    have e1 : Real.pi * ((1 : Fin 4).val : ℝ) / 2 = Real.pi / 2 := by simp
    have e2 : Real.pi * ((2 : Fin 4).val : ℝ) / 2 = Real.pi := by simp
    have e3 : Real.pi * ((3 : Fin 4).val : ℝ) / 2 = Real.pi + Real.pi / 2 := by
      simp; ring
    unfold fourPhaseAverage
    rw [Fin.sum_univ_four, e0, e1, e2, e3]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;>
      simp [phaseRotation, Matrix.transpose_apply, Fin.sum_univ_four,
        Matrix.vecHead, Matrix.vecTail, Real.cos_add, Real.sin_add, hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2] <;>
      first | done | ring | skip
  have hsym : fourPhaseAverage sigma = phaseSymmetricMatrix a b c1 c2 := by
    rw [hmain]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phaseSymmetricMatrix, a, b, c1, c2] <;> ring
  refine ⟨hmain, hsym, ?_⟩
  set w : ℂ := ⟨c2, c1⟩ with hw
  have hn : ‖w‖ = z := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [z, hw]
    congr 1; ring
  refine ⟨Complex.arg w, ?_, ?_, ?_⟩
  · have := Complex.norm_mul_sin_arg w
    rw [hn] at this; simpa [hw] using this.symm
  · have := Complex.norm_mul_cos_arg w
    rw [hn] at this; simpa [hw] using this.symm
  · have h1 : z * Real.sin (Complex.arg w) = c1 := by
      have := Complex.norm_mul_sin_arg w
      rw [hn] at this; simpa [hw] using this
    have h2 : z * Real.cos (Complex.arg w) = c2 := by
      have := Complex.norm_mul_cos_arg w
      rw [hn] at this; simpa [hw] using this
    rw [h1, h2]; exact hsym


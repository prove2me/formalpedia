-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P30.controlled_z_update
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:29:00.364763+00:00
-- url     : https://prove2.me/submissions/6707521f-59b1-43a0-9efe-6e3e44389379

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

open QAlgorithms.Papers.Independent.Intake100.P30 in
theorem solution {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix (Fin 2) (Fin 2) ℂ) (R : Matrix J (Fin 2) ℂ) (W : Matrix J J ℂ)
    (hZ : ValidGraph (Matrix.fromBlocks T R.transpose R W)) (g : ℝ) :
    let C := g • twoEdge
    graphLocalMobius 1 0 C 1 (Matrix.fromBlocks T R.transpose R W) =
      Matrix.fromBlocks (T + complexify C) R.transpose R W ∧
    ValidGraph (Matrix.fromBlocks (T + complexify C) R.transpose R W) := by
  intro C
  have hc1 : complexify (1 : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) ℝ) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [complexify]
    · simp [complexify, Matrix.one_apply_ne h]
  have hc0 : complexify (0 : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) ℝ) = 0 := by
    ext i j
    simp [complexify]
  have hcC : complexify (Matrix.fromBlocks C 0 0 0 : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) ℝ) =
      Matrix.fromBlocks (complexify C) 0 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [complexify, Matrix.fromBlocks]
  have hCsym : ∀ a b : Fin 2, C a b = C b a := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  have hcCt : Matrix.transpose (complexify C) = complexify C := by
    ext a b
    show ((C b a : ℝ) : ℂ) = ((C a b : ℝ) : ℂ)
    rw [hCsym]
  refine ⟨?_, ?_, ?_⟩
  · unfold graphLocalMobius mobius
    rw [Matrix.fromBlocks_one, Matrix.fromBlocks_zero, hc1, hc0, hcC, Matrix.zero_mul, add_zero,
      inv_one, Matrix.mul_one, Matrix.one_mul, Matrix.fromBlocks_add, zero_add, zero_add,
      zero_add, add_comm (complexify C) T]
  · have hs := hZ.1
    unfold Matrix.IsSymm at hs ⊢
    rw [Matrix.fromBlocks_transpose] at hs ⊢
    rw [Matrix.fromBlocks_inj] at hs
    obtain ⟨hT, _, _, hW⟩ := hs
    rw [Matrix.transpose_add, hT, hcCt, Matrix.transpose_transpose, hW]
  · have him : imagPart (Matrix.fromBlocks (T + complexify C) R.transpose R W) =
        imagPart (Matrix.fromBlocks T R.transpose R W) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [imagPart, Matrix.fromBlocks, complexify]
    rw [him]
    exact hZ.2

end

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P30.local_shear
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:29:49.857197+00:00
-- url     : https://prove2.me/submissions/d86181af-9b0d-4967-9c51-8a1f8b872af5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

open QAlgorithms.Papers.Independent.Intake100.P30 in
theorem solution {J : Type*} [Fintype J] [DecidableEq J]
    (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) (hZ : ValidGraph (oneGraph t r W)) (g : ℝ) :
    oneAction 1 0 g 1 (oneGraph t r W) = oneGraph (t + (g : ℂ)) r W ∧
    ValidGraph (oneGraph (t + (g : ℂ)) r W) := by
  have hA : complexify (Matrix.fromBlocks (fun _ _ => (1:ℝ)) 0 0 1 :
      Matrix (Unit ⊕ J) (Unit ⊕ J) ℝ) = 1 := by
    ext i j
    rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j
    · simp [complexify, Matrix.fromBlocks, Matrix.one_apply]
    · simp [complexify, Matrix.fromBlocks, Matrix.one_apply]
    · simp [complexify, Matrix.fromBlocks, Matrix.one_apply]
    · by_cases h : i = j <;> simp [complexify, Matrix.fromBlocks, Matrix.one_apply, h]
  have hB : complexify (Matrix.fromBlocks (fun _ _ => (0:ℝ)) 0 0 0 :
      Matrix (Unit ⊕ J) (Unit ⊕ J) ℝ) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [complexify, Matrix.fromBlocks]
  have h1 : oneAction 1 0 g 1 (oneGraph t r W) = oneGraph (t + (g : ℂ)) r W := by
    unfold oneAction graphLocalMobius mobius
    rw [hA, hB, Matrix.zero_mul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [complexify, oneGraph, Matrix.fromBlocks, add_comm]
  refine ⟨h1, ?_⟩
  obtain ⟨hs, hp⟩ := hZ
  have him : imagPart (oneGraph (t + (g : ℂ)) r W) = imagPart (oneGraph t r W) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [imagPart, oneGraph, Matrix.fromBlocks]
  refine ⟨?_, by rw [him]; exact hp⟩
  apply Matrix.IsSymm.ext
  intro i j
  have := hs.apply i j
  rcases i with i | i <;> rcases j with j | j <;> simpa [oneGraph, Matrix.fromBlocks] using this

end

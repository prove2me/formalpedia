-- Prove2me | solution 1 for RadGauss.LipschitzGaussian.theorem_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:53:52.258249+00:00
-- url     : https://prove2.me/submissions/1a8b352f-c498-41b3-8e57-41203ed93a94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity
import Definitions.Def_RadGauss_LipschitzGaussian_Classes
import Definitions.Def_RadGauss_LipschitzGaussian_cubeExtension
import Theorems.Thm_RadGauss_LipschitzGaussian_theorem_14
import Theorems.Thm_RadGauss_LipschitzGaussian_cubeExtension_spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open RadGauss.LipschitzGaussian in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) (g : (Fin k → ℤˣ) → ℤˣ) (F : Fin k → Set (X → ℤˣ)) (n : ℕ)
    (hmeas : ∀ j, AEMeasurable (RadGauss.LipschitzGaussian.empiricalGaussian n
      (RadGauss.LipschitzGaussian.signClass (F j))) (Measure.pi fun _ : Fin n => μ)) :
    RadGauss.LipschitzGaussian.gaussianComplexity μ n (RadGauss.LipschitzGaussian.boolComb g F) ≤
      2 * ∑ j, RadGauss.LipschitzGaussian.gaussianComplexity μ n
        (RadGauss.LipschitzGaussian.signClass (F j)) := by
  obtain ⟨-, hvert, hrange, hz, hlip⟩ := cubeExtension_spec hk g
  let Fv : Set (X → EuclideanSpace ℝ (Fin k)) :=
    {v | ∃ f : Fin k → X → ℤˣ, (∀ j, f j ∈ F j) ∧ v = fun x => cubeVertex (fun j => f j x)}
  have hDS : SubsetDirectSum Fv (fun j => signClass (F j)) := by
    rintro v ⟨f, hf, rfl⟩ j
    exact ⟨f j, hf j, rfl⟩
  let φ : Unit → EuclideanSpace ℝ (Fin k) → ℝ := fun _ => cubeExtension g
  have hbdd : ∃ M : ℝ, ∀ y a, |φ y a| ≤ M := ⟨1, fun _ a => abs_le.2 (hrange a)⟩
  have hpt : ∀ x : Fin n → X, empiricalGaussian n (boolComb g F) x ≤
      2 * ∑ j, empiricalGaussian n (signClass (F j)) x := by
    intro x
    have h14 := theorem_14 Fv (fun j => signClass (F j)) hDS φ 1 (fun _ => hlip) (fun _ => hz)
      hbdd n (fun i => (x i, ()))
    simp only [ENNReal.coe_one, mul_one] at h14
    refine le_trans ?_ h14
    unfold empiricalGaussian
    refine lintegral_mono fun gv => ?_
    refine iSup₂_le fun h hh => ?_
    obtain ⟨f, hf, rfl⟩ := hh
    refine le_iSup₂_of_le (fun z : X × Unit => cubeExtension g (cubeVertex (fun j => f j z.1)))
      ⟨_, ⟨f, hf, rfl⟩, rfl⟩ (le_of_eq ?_)
    simp only [hvert, signToReal]
  calc gaussianComplexity μ n (boolComb g F)
      ≤ ∫⁻ x, 2 * ∑ j, empiricalGaussian n (signClass (F j)) x
          ∂(Measure.pi fun _ : Fin n => μ) := lintegral_mono hpt
    _ = 2 * ∑ j, gaussianComplexity μ n (signClass (F j)) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_finsetSum' _ (fun j _ => hmeas j)]
      rfl

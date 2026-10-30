-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.tangentMapThroughCurve
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:14:17.80799+00:00
-- url     : https://prove2.me/submissions/fd91e5f5-3e29-449d-8425-1790d97c1b8f

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (i : N → H) (hi : IsSmoothHilbertEmbedding (E := F) i) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ gamma) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) i (f (gamma 0))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 (1 : ℝ))) =
      deriv (fun t => i (f (gamma t))) 0 := by
  have hi1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, H) i (f (gamma 0)) :=
    (hi.1.mdifferentiable (by simp)) _
  have hf1 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f (gamma 0) :=
    (hf.mdifferentiable (by simp)) _
  have hg1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 :=
    (hgamma.mdifferentiable (by simp)) _
  have h1 := mfderiv_comp (0 : ℝ) hf1 hg1
  have h2 := mfderiv_comp (0 : ℝ) hi1 (hf1.comp (0 : ℝ) hg1)
  rw [mfderiv_eq_fderiv, h1] at h2
  rw [← fderiv_apply_one_eq_deriv]
  change _ = fderiv ℝ (i ∘ (f ∘ gamma)) 0 1
  rw [h2]
  rfl
end

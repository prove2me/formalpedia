-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-16T05:39:39.865683+00:00
-- url     : https://prove2.me/submissions/321135a3-04e3-464e-bb21-6d8cb023b439

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm
import Theorems.Thm_PersistClust_Count_theorem_4_5_net38
import Theorems.Thm_PersistClust_Count_theorem_4_8_core_free
import Theorems.Thm_PersistClust_Count_theorem_4_8_netting_38

open MeasureTheory Bundle
open scoped ContDiff Manifold

open PersistClust.Count

/-- **Theorem 4.8 of RR-6968, as stated.** If the sample is a geodesic `3δ/8`-sample of
`𝔽^{cδ}`, Theorem 4.5 (from a `3δ/8`-sample) gives the multi-bijection γ at threshold and
radius `cδ`, and the deterministic core forces the right cluster count for every sort order;
so the failure event lies inside the netting failure, whose probability is bounded by the
original right-hand side (external covering number, `𝔽^{cδ}`-centred ball measure). -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X] [MeasurableSpace X] [BorelSpace X]
    (hconv : 0 < convexityRadius X)
    (f : X → ℝ) (c : ℝ) (hc : 0 < c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (hdens : IsDensity (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f) (htame : IsTame0 f)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hsep : IsSeparated (diagram0 f) d₁ d₂)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) (n : ℕ) :
    sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
        {pts | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (δ / 8)
              (superlevel f (c * δ))) := by
  classical
  have hdecomp : {pts : Fin n → X | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ⊆ {pts : Fin n → X |
          ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)} := by
    intro pts hfail hnet
    obtain ⟨L, hLdef⟩ : ∃ L : Finset X, L = Finset.image pts Finset.univ := ⟨_, rfl⟩
    have hmem : ∀ i : Fin n, pts i ∈ L := by
      intro i
      rw [hLdef]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hsurj : ∀ x ∈ L, ∃ i : Fin n, pts i = x := by
      intro x hx
      rw [hLdef] at hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact ⟨i, hi⟩
    have hnetL : IsGeodesicSample (L : Set X) (superlevel f (c * δ)) (3 * δ / 8) := by
      intro y hyY
      obtain ⟨v, hv, hdv⟩ := hnet y hyY
      obtain ⟨i, hi⟩ := Set.mem_range.mp hv
      refine ⟨pts i, ?_, ?_⟩
      · rw [Finset.mem_coe]
        exact hmem i
      · rw [hi]
        exact hdv
    obtain ⟨γ, hγ⟩ := theorem_4_5_net38 (I := I) hconv L f c hc.le hLip htame δ hδ hδρ
      (c * δ) hnetL
    exact hfail (theorem_4_8_core_free (I := I) hconv f c hc hLip hdens htame d₁ d₂ hd₁ hd
      hsep δ hδ hδρ hδc τ hτ₁ hτ₂ n pts L hmem hsurj γ hγ)
  exact (measure_mono hdecomp).trans
    (theorem_4_8_netting_38 (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f c δ hc hδ n hLip hdens)

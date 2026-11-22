-- Prove2me | solution 1 for SobolevL2.sobolev_complete
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:33:19.184617+00:00
-- url     : https://prove2.me/submissions/a9cd65fa-b2fb-417a-87b9-c3f798ee2239

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

open SobolevL2

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : ℕ → 𝓢'(E, F))
    (hu : ∀ n, MemSobolev s 2 (u n))
    (hCauchy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, sobolevNorm s (u m - u n) < ε) :
    ∃ v : 𝓢'(E, F), MemSobolev s 2 v ∧
      Tendsto (fun n => sobolevNorm s (u n - v)) atTop (𝓝 0) := by
  -- the embedding `L² → 𝓢'` is injective
  have hinj : Function.Injective
      (fun f : Lp F 2 (volume : Measure E) => (f : 𝓢'(E, F))) := by
    have h := LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E))
        (p := 2))
    exact h
  -- the Sobolev norm is the `L²` norm of the representative of `J^s w`
  have key : ∀ (w : 𝓢'(E, F)) (f : Lp F 2 (volume : Measure E)),
      besselPotential E F s w = f → sobolevNorm s w = ‖f‖ₑ := by
    intro w f hf
    unfold sobolevNorm
    apply le_antisymm
    · exact iInf₂_le f hf
    · refine le_iInf₂ fun g hg => ?_
      have hfg : f = g := hinj (hf.symm.trans hg)
      rw [hfg]
  choose f hf using hu
  have hsub : ∀ (n : ℕ) (w : 𝓢'(E, F)) (g : Lp F 2 (volume : Measure E)),
      besselPotential E F s w = g →
        besselPotential E F s (u n - w) = ((f n - g : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    intro n w g hg
    rw [map_sub, hf n, hg, ← Lp.toTemperedDistributionCLM_apply,
      ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_sub]
  have hnorm : ∀ m n, sobolevNorm s (u m - u n) = edist (f m) (f n) := by
    intro m n
    rw [key _ _ (hsub m (u n) (f n) (hf n)), edist_eq_enorm_sub]
  have hC : CauchySeq f := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy ε hε
    exact ⟨N, fun m hm n hn => (hnorm m n) ▸ hN m hm n hn⟩
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hC
  have hv : besselPotential E F s (besselPotential E F (-s) (g : 𝓢'(E, F))) = g := by
    rw [besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero]
    rfl
  refine ⟨besselPotential E F (-s) (g : 𝓢'(E, F)), ⟨g, hv⟩, ?_⟩
  have h2 : ∀ n, sobolevNorm s (u n - besselPotential E F (-s) (g : 𝓢'(E, F))) =
      edist (f n) g := by
    intro n
    rw [key _ _ (hsub n _ g hv), edist_eq_enorm_sub]
  simp_rw [h2]
  exact (tendsto_iff_edist_tendsto_0.mp hg)

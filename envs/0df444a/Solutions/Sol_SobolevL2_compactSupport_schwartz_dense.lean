-- Prove2me | solution 1 for SobolevL2.compactSupport_schwartz_dense
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:40:01.137337+00:00
-- url     : https://prove2.me/submissions/e666e2f8-6ab3-4889-8e86-f621d51ca9f8

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm
import Theorems.Thm_SchwartzDist_dense_setOf_hasCompactSupport

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

open SobolevL2

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢'(E, F)) (hu : MemSobolev s 2 u)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : 𝓢(E, F), HasCompactSupport (φ : E → F) ∧
      sobolevNorm s (u - (φ : 𝓢'(E, F))) < ε := by
  -- the embedding `L² → 𝓢'` is injective
  have hinj : Function.Injective
      (fun f : Lp F 2 (volume : Measure E) => (f : 𝓢'(E, F))) :=
    LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E))
        (p := 2))
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
  -- the Bessel potential on Schwartz functions
  let M : ℝ → 𝓢(E, F) →L[ℂ] 𝓢(E, F) := fun r =>
    SchwartzMap.fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
  have hJ : ∀ (r : ℝ) (φ : 𝓢(E, F)),
      besselPotential E F r (φ : 𝓢'(E, F)) = ((M r φ : 𝓢(E, F)) : 𝓢'(E, F)) := by
    intro r φ
    rw [besselPotential, fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  -- `T = J^s : 𝓢 → L²`, a continuous linear map
  let T : 𝓢(E, F) →L[ℂ] Lp F 2 (volume : Measure E) :=
    (SchwartzMap.toLpCLM ℂ F 2 (volume : Measure E)).comp (M s)
  have hT : ∀ φ : 𝓢(E, F),
      besselPotential E F s (φ : 𝓢'(E, F)) = ((T φ : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    intro φ
    rw [hJ]
    simp only [T, ContinuousLinearMap.coe_comp, Function.comp_apply,
      SchwartzMap.toLpCLM_apply, Lp.toTemperedDistribution_toLp_eq]
  -- `T` has dense range: its range contains all Schwartz functions
  have hdense : DenseRange T := by
    have h0 := SchwartzMap.denseRange_toLpCLM (E := E) (F := F) (p := 2)
      (μ := (volume : Measure E)) (by norm_num)
    refine h0.mono ?_
    rintro _ ⟨ψ, rfl⟩
    refine ⟨M (-s) ψ, hinj ?_⟩
    simp only
    rw [← hT, ← hJ, besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
      SchwartzMap.toLpCLM_apply, Lp.toTemperedDistribution_toLp_eq]
    rfl
  obtain ⟨f, hf⟩ := hu
  have hD : Dense (T '' {φ : 𝓢(E, F) | HasCompactSupport (φ : E → F)}) :=
    hdense.dense_image T.continuous (SchwartzDist.dense_setOf_hasCompactSupport (E := E) (F := F))
  obtain ⟨g, ⟨φ, hφ, rfl⟩, hlt⟩ := EMetric.mem_closure_iff.mp (hD f) ε hε
  refine ⟨φ, hφ, ?_⟩
  have hsub : besselPotential E F s (u - (φ : 𝓢'(E, F))) =
      ((f - T φ : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    rw [map_sub, hf, hT, ← Lp.toTemperedDistributionCLM_apply,
      ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_sub]
  rw [key _ _ hsub, ← edist_eq_enorm_sub]
  exact hlt

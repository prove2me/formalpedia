-- Prove2me | solution 1 for PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.propagate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:06.463604+00:00
-- url     : https://prove2.me/submissions/719c42f2-b44b-450b-95a6-b62915fc0049

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
namespace PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
theorem _root_.solution (f g : ℂ → ℂ) (a b : ℝ) (hf : ∀ σ : ℝ, a < σ → AnalyticAt ℂ f σ)
    (hg : ∀ σ : ℝ, a < σ → AnalyticAt ℂ g σ) (he : ∀ σ : ℝ, b < σ → f σ = g σ) :
    ∀ σ : ℝ, a < σ → f =ᶠ[𝓝 (σ : ℂ)] g := by
  have key : ∀ σ : ℝ, a < σ → (∃ᶠ z in 𝓝[≠] (σ : ℂ), (f - g) z = 0) → f =ᶠ[𝓝 (σ : ℂ)] g := by
    intro σ hσ hfr
    have := ((hf σ hσ).sub (hg σ hσ)).frequently_zero_iff_eventually_zero.1 hfr
    filter_upwards [this] with z hz
    exact sub_eq_zero.1 hz
  have fr : ∀ σ : ℝ, (∀ τ : ℝ, σ < τ → τ < σ + 1 → f τ = g τ) → ∃ᶠ z in 𝓝[≠] (σ : ℂ), (f - g) z = 0 := by
    intro σ hτ
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n : ℕ => σ + 1 / ((n : ℝ) + 2)) atTop (𝓝 σ) := by
      simpa using (tendsto_const_nhds (x := σ)).add h1
    have ht : Tendsto (fun n : ℕ => ((σ + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (σ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto σ).comp h2) (Eventually.of_forall fun n => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have h3 := Complex.ofReal_injective h
      have h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    simp only [Pi.sub_apply, sub_eq_zero]
    have h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have h5 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact hτ _ (by linarith) (by linarith)
  have good : ∀ τ : ℝ, max a b < τ → f =ᶠ[𝓝 (τ : ℂ)] g := fun τ hτ =>
    key τ (lt_of_le_of_lt (le_max_left _ _) hτ)
      (fr τ fun t ht _ => he t (by linarith [le_max_right a b]))
  intro σ hσ
  by_contra hne
  set B := {τ : ℝ | a < τ ∧ ¬ (f =ᶠ[𝓝 (τ : ℂ)] g)} with hB
  have hBne : σ ∈ B := ⟨hσ, hne⟩
  have hBbdd : BddAbove B := ⟨max a b, fun τ hτ => by
    by_contra h
    push_neg at h
    exact hτ.2 (good τ h)⟩
  set γ := sSup B with hγdef
  have hγσ : σ ≤ γ := le_csSup hBbdd hBne
  have hγa : a < γ := lt_of_lt_of_le hσ hγσ
  have above : ∀ τ : ℝ, γ < τ → f =ᶠ[𝓝 (τ : ℂ)] g := fun τ hτ => by
    by_contra h
    exact absurd (le_csSup hBbdd ⟨by linarith, h⟩) (not_le.2 hτ)
  have hγ : f =ᶠ[𝓝 (γ : ℂ)] g := key γ hγa (fr γ fun t ht _ => (above t ht).eq_of_nhds)
  have h1 : ∀ᶠ z in 𝓝 (γ : ℂ), f =ᶠ[𝓝 z] g := Filter.Eventually.eventually_nhds hγ
  have h2 : ∀ᶠ τ in 𝓝 γ, f =ᶠ[𝓝 ((τ : ℝ) : ℂ)] g := (Complex.continuous_ofReal.tendsto γ).eventually h1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h2
  obtain ⟨τ, hτB, hτ⟩ := exists_lt_of_lt_csSup ⟨σ, hBne⟩ (show γ - δ < γ by linarith)
  have hτγ : τ ≤ γ := le_csSup hBbdd hτB
  exact hτB.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith))
end PositivityTheory.RgJS.LandauNonnegativeDirichletSeries

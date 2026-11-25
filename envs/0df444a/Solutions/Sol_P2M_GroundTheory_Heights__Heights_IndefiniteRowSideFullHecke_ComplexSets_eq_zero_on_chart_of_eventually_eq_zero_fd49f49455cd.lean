-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_on_chart_of_eventually_eq_zero_fd49f49455cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:57.476491+00:00
-- url     : https://prove2.me/submissions/974d8602-e1ec-450a-8f90-747c23c1be41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {Y V : Set (σ → ℂ)} {d : ℕ}
    {B : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → σ → ℂ} (hBo : IsOpen B) (hBc : IsPreconnected B)
    (hg : AnalyticOnNhd ℂ g B) (hYV : Y ∩ V = g '' B) (F : (σ → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F V)
    (h0 : ∃ y ∈ Y ∩ V, ∀ᶠ u in 𝓝 y, u ∈ Y → F u = 0) : ∀ u ∈ Y ∩ V, F u = 0 := by
  obtain ⟨y, hy, hyF⟩ := h0
  have hgB : ∀ t ∈ B, g t ∈ Y ∩ V := fun t ht => by rw [hYV]; exact ⟨t, ht, rfl⟩
  have hy' : y ∈ g '' B := by rw [← hYV]; exact hy
  obtain ⟨t₀, ht₀, rfl⟩ := hy'
  have hFg : AnalyticOnNhd ℂ (F ∘ g) B := fun t ht => (hF (g t) (hgB t ht).2).comp (hg t ht)
  have hev : F ∘ g =ᶠ[𝓝 t₀] 0 := by
    filter_upwards [(hg t₀ ht₀).continuousAt.tendsto.eventually hyF, hBo.mem_nhds ht₀] with t ht htB
    exact ht (hgB t htB).1
  have hzero := hFg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc ht₀ hev
  intro u hu
  have hu' : u ∈ g '' B := by rw [← hYV]; exact hu
  obtain ⟨t, ht, rfl⟩ := hu'
  exact hzero ht
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

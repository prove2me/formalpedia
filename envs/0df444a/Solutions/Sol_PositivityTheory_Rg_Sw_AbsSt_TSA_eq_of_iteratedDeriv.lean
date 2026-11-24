-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.AbsSt.TSA.eq_of_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:27.646879+00:00
-- url     : https://prove2.me/submissions/2cd14748-1f64-4f69-b270-53234386c725

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_IteratedDerivOfReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.TSA
namespace PositivityTheory.Rg.Sw.AbsSt.TSA
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h : ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0) (t : ℝ) : f t = g t := by
  have h0U : (0 : ℂ) ∈ U := by simpa using hmem 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hnear : f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball), ← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball)]
    simp_rw [h]
  set V := connectedComponentIn U (0 : ℂ)
  have hVo : IsOpen V := hU.connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have h0V : (0 : ℂ) ∈ V := mem_connectedComponentIn h0U
  have hRV : range (fun x : ℝ => (x : ℂ)) ⊆ V := by
    apply (isPreconnected_range Complex.continuous_ofReal).subset_connectedComponentIn
    · exact ⟨0, by simp⟩
    · rintro _ ⟨x, rfl⟩; exact hmem x
  have hVU : V ⊆ U := connectedComponentIn_subset _ _
  have hfa : AnalyticOnNhd ℂ f V := (hf.mono hVU).analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := (hg.mono hVU).analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc h0V hnear (hRV ⟨t, rfl⟩)
end PositivityTheory.Rg.Sw.AbsSt.TSA

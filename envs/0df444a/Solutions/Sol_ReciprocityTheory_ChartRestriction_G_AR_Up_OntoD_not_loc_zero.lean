-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.not_loc_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:53.041981+00:00
-- url     : https://prove2.me/submissions/1cbd6d55-7f37-44b4-9166-830531c4ee53

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_ident


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set Metric
noncomputable section
variable {n : ℕ} {Ω : Set (V n)} {g : V n → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD
theorem _root_.solution (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : ∀ z ∈ Ω, ¬ g =ᶠ[𝓝 z] 0 := by
  intro z hz hzero
  obtain ⟨z0, hz0, hgz0⟩ := hne
  set u := {w : V n | ∀ᶠ y in 𝓝 w, g y = (0 : V n → ℂ) y} with hu_def
  set v := {w : V n | ∀ᶠ y in 𝓝 w, ¬ (g =ᶠ[𝓝 y] 0)} with hv_def
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen v := isOpen_setOfPred_eventually_nhds
  have hcov : Ω ⊆ u ∪ v := by
    intro w hw
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ w hw
    have hfr : ∃ᶠ y in 𝓝 w, g =ᶠ[𝓝 y] 0 := by
      rw [Filter.Frequently]; intro h; exact hnv h
    obtain ⟨y, hy1, hy2⟩ := (hfr.and_eventually (ball_mem_nhds w hρ)).exists
    have hB0 := C.ident n (ball w ρ) g y isOpen_ball (convex_ball w ρ) (hg.mono hB) hy2 hy1
    exact hnu (Filter.eventually_of_mem (ball_mem_nhds w hρ) fun x hx => hB0 hx)
  have hv0 : z0 ∈ v := by
    have hct : ContinuousAt g z0 := hg.continuousOn.continuousAt (hΩ.mem_nhds hz0)
    have hev : ∀ᶠ y in 𝓝 z0, g y ≠ 0 := hct.eventually_ne hgz0
    exact hev.mono fun y hy h => hy (by simpa using h.eq_of_nhds)
  obtain ⟨w, -, hwu, hwv⟩ := hc u v hu hv hcov ⟨z, hz, hzero⟩ ⟨z0, hz0, hv0⟩
  obtain ⟨y, hy1, hy2⟩ := ((Filter.Eventually.eventually_nhds hwu).and hwv).exists
  exact hy2 hy1
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD

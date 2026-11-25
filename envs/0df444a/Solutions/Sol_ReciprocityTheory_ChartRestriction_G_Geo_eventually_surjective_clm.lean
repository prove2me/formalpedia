-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eventually_surjective_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:14.306478+00:00
-- url     : https://prove2.me/submissions/419629a2-f8a8-4159-9e51-a99b1737a741

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Set Filter Topology Module
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {Y : Type*} [TopologicalSpace Y] {A : Y → (Fin e → ℂ) →L[ℂ] F}
    {y0 : Y} (hA : ContinuousAt A y0) (h0 : Function.Surjective (A y0)) :
    ∀ᶠ y in 𝓝 y0, Function.Surjective (A y) := by
  obtain ⟨Bl, hBl⟩ := (A y0 : (Fin e → ℂ) →ₗ[ℂ] F).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr h0)
  set B : F →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap Bl
  have hB : (A y0).comp B = 1 := by
    ext1 v
    exact LinearMap.congr_fun hBl v
  have hc : ContinuousAt (fun y => (A y).comp B) y0 := hA.clm_comp continuousAt_const
  have hU : ∀ᶠ y in 𝓝 y0, IsUnit ((A y).comp B) :=
    hc.eventually (Units.isOpen.mem_nhds (by show IsUnit ((A y0).comp B); rw [hB]; exact isUnit_one))
  filter_upwards [hU] with y hy
  obtain ⟨S, hS⟩ := hy.exists_right_inv
  intro v
  refine ⟨B (S v), ?_⟩
  have := congrArg (fun T : F →L[ℂ] F => T v) hS
  simpa using this
end ReciprocityTheory.ChartRestriction.G.Geo

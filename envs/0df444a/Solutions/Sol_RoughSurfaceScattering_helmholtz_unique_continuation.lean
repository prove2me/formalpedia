-- Prove2me | solution 1 for RoughSurfaceScattering.helmholtz_unique_continuation
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:36:15.373815+00:00
-- url     : https://prove2.me/submissions/0e9e63be-1a79-4f08-9e00-f621e671255f

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_helmholtz_analytic

open MeasureTheory
open RoughSurfaceScattering

theorem solution (k : ℝ) (G : Set R2) (hG : IsOpen G)
    (hGc : IsConnected G) (u1 u2 : R2 → ℂ)
    (h1 : ContDiffOn ℝ 2 u1 G) (h2 : ContDiffOn ℝ 2 u2 G)
    (hH1 : IsHelmholtzOn G k u1) (hH2 : IsHelmholtzOn G k u2)
    (V : Set R2) (hV : IsOpen V) (hVne : V.Nonempty) (hVG : V ⊆ G)
    (heq : ∀ x ∈ V, u1 x = u2 x) :
    ∀ x ∈ G, u1 x = u2 x := by
  have ha := (helmholtz_analytic k G hG u1 h1 hH1).sub (helmholtz_analytic k G hG u2 h2 hH2)
  obtain ⟨z0, hz0⟩ := hVne
  have hev : (u1 - u2) =ᶠ[nhds z0] 0 :=
    Filter.eventually_of_mem (hV.mem_nhds hz0) fun x hx => by
      simp [heq x hx]
  have hzero := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hGc.isPreconnected
    (hVG hz0) hev
  intro x hx
  exact sub_eq_zero.mp (hzero hx)

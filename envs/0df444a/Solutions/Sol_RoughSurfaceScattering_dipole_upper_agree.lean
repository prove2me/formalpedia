-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_upper_agree
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T03:03:10.596846+00:00
-- url     : https://prove2.me/submissions/99ea2d2f-a42c-4864-b611-95b5ddd0748c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_tsp_dipole_derivative

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp k1 k2 μ1 μ2 : ℝ)
    (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ1 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ2 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) (u1 u2 : (R2 → ℂ) × (R2 → ℂ))
    (hu1 : IsTSPSolution f kp k1 μ1 (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u1.1 u1.2)
    (hu2 : IsTSPSolution f kp k2 μ2 (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u2.1 u2.2) :
    ∀ x ∈ Dplus f, u1.1 x = u2.1 x := by
  intro x hx
  have h1 := tsp_dipole_derivative f hf kp k1 μ1 hpar1 U1 hU1 z hz ν u1 hu1 x hx
  have h2 := tsp_dipole_derivative f hf kp k2 μ2 hpar2 U2 hU2 z hz ν u2 hu2 x hx
  have hO : IsOpen (Dplus f) := isOpen_lt (hf.1.continuous.comp (by fun_prop)) (by fun_prop)
  have hc : Continuous fun t : ℝ => z - t • ν := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), z - t • ν ∈ Dplus f := by
    have := hc.tendsto 0
    simp only [zero_smul, sub_zero] at this
    exact this.eventually (hO.mem_nhds hz)
  have heq : (fun t : ℝ => (U1 (z - t • ν)).1 x) =ᶠ[𝓝 0] fun t => (U2 (z - t • ν)).1 x := by
    filter_upwards [hev] with t ht
    exact hagree x hx _ ht
  exact h1.unique (h2.congr_of_eventuallyEq heq)

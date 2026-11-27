-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_upper_agree_cross
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T03:04:13.894807+00:00
-- url     : https://prove2.me/submissions/4091e70c-3d69-44ab-8989-f3685b7957b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_tsp_dipole_derivative

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x)
    (z : R2) (hz : z ∈ Dplus f1 ∩ Dplus f2) (ν : R2) (u1 u2 : (R2 → ℂ) × (R2 → ℂ))
    (hu1 : IsTSPSolution f1 kp k1 μ1 (incData f1 (dipoleSource kp z ν)).1
      (incData f1 (dipoleSource kp z ν)).2 u1.1 u1.2)
    (hu2 : IsTSPSolution f2 kp k2 μ2 (incData f2 (dipoleSource kp z ν)).1
      (incData f2 (dipoleSource kp z ν)).2 u2.1 u2.2) :
    ∀ x ∈ Dplus f1 ∩ Dplus f2, u1.1 x = u2.1 x := by
  intro x hx
  have h1 := tsp_dipole_derivative f1 hf1 kp k1 μ1 hpar1 U1 hU1 z hz.1 ν u1 hu1 x hx.1
  have h2 := tsp_dipole_derivative f2 hf2 kp k2 μ2 hpar2 U2 hU2 z hz.2 ν u2 hu2 x hx.2
  have hO : IsOpen (Dplus f1 ∩ Dplus f2) :=
    (isOpen_lt (hf1.1.continuous.comp (by fun_prop)) (by fun_prop)).inter
      (isOpen_lt (hf2.1.continuous.comp (by fun_prop)) (by fun_prop))
  have hc : Continuous fun t : ℝ => z - t • ν := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), z - t • ν ∈ Dplus f1 ∩ Dplus f2 := by
    have := hc.tendsto 0
    simp only [zero_smul, sub_zero] at this
    exact this.eventually (hO.mem_nhds hz)
  have heq : (fun t : ℝ => (U1 (z - t • ν)).1 x) =ᶠ[𝓝 0] fun t => (U2 (z - t • ν)).1 x := by
    filter_upwards [hev] with t ht
    exact hagree x hx _ ht
  exact h1.unique (h2.congr_of_eventuallyEq heq)

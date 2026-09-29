-- Prove2me | solution 1 for SenTachyon.minimumEnergyDensity_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T23:43:06.502369+00:00
-- url     : https://prove2.me/submissions/20b344a7-c9db-4c2e-bf44-24d0cc5cf190

import Mathlib
import Definitions.Def_SenTachyon_Defs

set_option autoImplicit false

open SenTachyon Filter Topology in
theorem solution (g : ℝ) (hg : 0 < g) :
    Tendsto (fun R : ℝ × ℝ => minimumEnergyDensity R.1 R.2 g) (atTop ×ˢ atTop) (𝓝 0) := by
  have hc : 0 < 2 * Real.pi ^ 2 * g := by positivity
  have hprod : Tendsto (fun R : ℝ × ℝ => R.1 * R.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  have h2 : Tendsto (fun R : ℝ × ℝ => (2 * Real.pi ^ 2 * g * (R.1 * R.2))⁻¹)
      (atTop ×ˢ atTop) (𝓝 0) :=
    (hprod.const_mul_atTop hc).inv_tendsto_atTop
  refine h2.congr' ?_
  have hev : ∀ᶠ R : ℝ × ℝ in atTop ×ˢ atTop, 0 < R.1 ∧ 0 < R.2 :=
    (eventually_gt_atTop 0).prod_mk (eventually_gt_atTop 0)
  filter_upwards [hev] with R hR
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hg' : g ≠ 0 := hg.ne'
  have h₁' : R.1 ≠ 0 := hR.1.ne'
  have h₂' : R.2 ≠ 0 := hR.2.ne'
  unfold minimumEnergyDensity minimumMass twoBraneMass dbraneTension torusArea dualRadius
    dualCoupling
  field_simp
  ring

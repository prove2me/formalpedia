-- Prove2me | solution 2 for SpherePacking.rescale_upper_packing_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:05.494852+00:00
-- url     : https://prove2.me/submissions/0a67a1a1-6c72-4391-9b54-54fecdf4175b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking


theorem solution {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).upperPackingDensity = S.upperPackingDensity := by
  unfold SpherePacking.upperPackingDensity
  have h : (fun R => (S.rescaleConfiguration hc).densityInsideRadius R) =
      S.densityInsideRadius ∘ (fun R : ℝ => R * c⁻¹) := by
    funext R
    simp [div_eq_mul_inv]
  have hm : Filter.map (fun R : ℝ => R * c⁻¹) atTop = atTop :=
    (OrderIso.mulRight₀ c⁻¹ (inv_pos.2 hc)).map_atTop
  rw [show (S.rescaleConfiguration hc).densityInsideRadius =
    (fun R => (S.rescaleConfiguration hc).densityInsideRadius R) from rfl, h,
    Filter.limsup_comp, hm]


-- Prove2me | solution 1 for RoughSurfaceScattering.tsp_halfplane_uniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-26T15:11:55.241233+00:00
-- url     : https://prove2.me/submissions/ee067724-7274-444c-9622-4dc861531dbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_tsp_upper_trace_representation

open MeasureTheory
open RoughSurfaceScattering

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1)
    (hf2 : IsBC1Alpha 1 f2) (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1)
    (hpar2 : ParamCond kp k2 μ2) (g11 g12 g21 g22 : ℝ → ℂ) (u1p u1m u2p u2m : R2 → ℂ)
    (hu1 : IsTSPSolution f1 kp k1 μ1 g11 g12 u1p u1m)
    (hu2 : IsTSPSolution f2 kp k2 μ2 g21 g22 u2p u2m)
    (c : ℝ) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (hline : ∀ t : ℝ, u1p (pt t c) = u2p (pt t c)) :
    ∀ x : R2, c ≤ x 1 → u1p x = u2p x := by
  intro x hx
  rcases hx.lt_or_eq with hx | hx
  · have hxU : x ∈ Uplus c := hx
    rw [tsp_upper_trace_representation f1 hf1 kp k1 μ1 hpar1 g11 g12 u1p u1m hu1 c hc1 x hxU,
      tsp_upper_trace_representation f2 hf2 kp k2 μ2 hpar2 g21 g22 u2p u2m hu2 c hc2 x hxU]
    simp only [hline]
  · have hxe : x = pt (x 0) c := by
      ext i; fin_cases i <;> simp [pt, hx]
    rw [hxe]; exact hline _

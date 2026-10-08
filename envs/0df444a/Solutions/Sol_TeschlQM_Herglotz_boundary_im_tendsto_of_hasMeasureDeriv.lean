-- Prove2me | solution 1 for TeschlQM.Herglotz.boundary_im_tendsto_of_hasMeasureDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T22:04:36.704147+00:00
-- url     : https://prove2.me/submissions/8da8fdb9-3ce0-4954-b426-be8166c803ab

import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Theorems.Thm_TeschlQM_Herglotz_deriv_le_boundary_im

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) (d : ℝ≥0∞)
    (hd : HasMeasureDeriv μ t d) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal
      ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi))
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  have h := deriv_le_boundary_im μ t
  have hl : lowerDeriv μ t = d := hd.liminf_eq
  have hu : upperDeriv μ t = d := hd.limsup_eq
  exact tendsto_of_le_liminf_of_limsup_le (hl ▸ h.1) (hu ▸ h.2.2)

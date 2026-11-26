-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_profileRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:53.485345+00:00
-- url     : https://prove2.me/submissions/7b2697d8-3c83-4fbe-9a02-fb863e750862

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
attribute [local simp] Sqrt6KissingBound.mem_tailBall

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet (profileRegion d s g) := by
  have hnorm : Measurable fun p : ℝ × (Fin d → ℝ) =>
      ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin d))‖ :=
    (continuous_norm.comp
      ((PiLp.continuous_toLp 2 _).comp continuous_snd)).measurable
  have hsecond : MeasurableSet
      {p : ℝ × (Fin d → ℝ) |
        ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin d))‖ < g p.1} :=
    measurableSet_lt hnorm (hg.comp measurable_fst)
  rw [show profileRegion d s g =
      {p : ℝ × (Fin d → ℝ) | p.1 ∈ s} ∩
        {p | ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin d))‖ < g p.1} by
    ext p
    simp [profileRegion]]
  exact (hs.preimage measurable_fst).inter hsecond
end Sqrt6KissingBound

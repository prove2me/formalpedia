-- Prove2me | solution 1 for Sqrt6KissingBound.volume_profileRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:37.615968+00:00
-- url     : https://prove2.me/submissions/ddcae66c-d321-4b64-8fc3-942a0e516b01

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_volume_tailBall
import Theorems.Thm_Sqrt6KissingBound_measurableSet_profileRegion
attribute [local simp] Sqrt6KissingBound.mem_tailBall

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (ℝ × (Fin d → ℝ))) (profileRegion d s g) =
      ∫⁻ t in s, (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (g t)) := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_profileRegion d hs hg)]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ s
  · have hfiber :
        Prod.mk t ⁻¹' profileRegion d s g = tailBall d (g t) := by
      ext v
      simp [profileRegion, ht]
    simp only [Set.indicator_of_mem ht]
    rw [hfiber]
    exact volume_tailBall d (g t)
  · simp [profileRegion, ht]
end Sqrt6KissingBound

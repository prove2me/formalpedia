-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_rotationalProfile_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:23:19.215313+00:00
-- url     : https://prove2.me/submissions/630baf78-69ca-4b62-a455-b2673cef7c85

import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Theorems.Thm_Sqrt6KissingBound_volume_rotationalProfile_Ioo


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 2)))).real
        (rotationalProfile (d + 1) (Set.Ioo a b) g) =
      (∫ t in a..b, g t ^ (d + 1)) * unitBallVolumeReal (d + 1) := by
  rw [Measure.real, volume_rotationalProfile_Ioo d hab hg hg0,
    ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal]
  · rfl
  · exact intervalIntegral.integral_nonneg hab fun t ht =>
      pow_nonneg (hg0 t ht) _
end Sqrt6KissingBound

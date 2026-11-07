-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_zone_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:11.41106+00:00
-- url     : https://prove2.me/submissions/a63a0e58-6c11-49b0-9ed3-b717b4eba276

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_zone


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (n : Sphere) {a b : ℝ} (hab : a ≤ b) :
    area (zone n a b) ≤ ENNReal.ofReal (2 * Real.pi * (b-a)) := by
  rw [area_zone n hab]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact max_le (sub_nonneg.mpr hab)
    (sub_le_sub (min_le_right _ _) (le_max_right _ _))
end QEC.Coding.ProbabilisticConstruction.SphericalCap

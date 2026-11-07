-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_zone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:15.369077+00:00
-- url     : https://prove2.me/submissions/c7bdbc45-d6dc-46c6-8346-25f5d8dded19

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_all
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_zone_ae_cap_difference
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capHeight_difference
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_ne_top
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {a b : ℝ} (hab : a ≤ b) :
    area (zone u a b) = ENNReal.ofReal (2 * Real.pi * max 0 (min 1 b - max (-1) a)) := by
  have hsub : cap u b ⊆ cap u a := fun s hs => hab.trans hs
  have hnonneg : 0 ≤ 2 * Real.pi * capHeight b :=
    mul_nonneg (by positivity) (show 0 ≤ capHeight b from le_max_left _ _)
  rw [measure_congr (zone_ae_cap_difference u a b),
    measure_diff hsub (measurableSet_cap u b).nullMeasurableSet (area_cap_ne_top u b),
    area_cap_all,area_cap_all,
    ← ENNReal.ofReal_sub _ hnonneg]
  congr 1
  rw [← mul_sub,capHeight_difference hab]
end QEC.Coding.ProbabilisticConstruction.SphericalCap

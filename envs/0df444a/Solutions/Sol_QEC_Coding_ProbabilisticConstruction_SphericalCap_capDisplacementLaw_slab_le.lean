-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_slab_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:14.492843+00:00
-- url     : https://prove2.me/submissions/cc9dffcc-d0ed-44bd-a722-0175135bde69

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_le_of_area_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_zone_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_slab
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_slab_preimage
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_zone


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R c h : ℝ} (hR : 0 < R)
    (u n : Sphere) (hc0 : -1 < c) (hc1 : c < 1) (d : ℝ) (hh : 0 ≤ h) :
    capDisplacementLaw R u c (slab n d h) ≤ ENNReal.ofReal (2*h/(R*(1-c))) := by
  rw [capDisplacementLaw,Measure.map_apply (by fun_prop) (measurableSet_slab n d h),
    displacement_slab_preimage hR]
  have hab : (d-h)/R ≤ (d+h)/R := (div_le_div_iff_of_pos_right hR).mpr (by linarith)
  have he : 2 * Real.pi * ((d+h)/R - (d-h)/R) = 4 * Real.pi * h / R := by ring
  have hb := area_zone_le n hab
  rw [he] at hb
  have hbound := capLaw_le_of_area_le u hc0 hc1 (measurableSet_zone n _ _) hb
  have hfactor : (4 * Real.pi * h / R) / (2 * Real.pi * (1-c)) =
      2*h/(R*(1-c)) := by field_simp [Real.pi_ne_zero, hR.ne', (sub_pos.mpr hc1).ne']; ring
  rwa [hfactor] at hbound
end QEC.Coding.ProbabilisticConstruction.SphericalCap

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_closedBall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:05.066389+00:00
-- url     : https://prove2.me/submissions/d4f0d998-be5c-4044-b2db-47ac2965bc58

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_ball_preimage
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_chord_cap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_le_of_area_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R c ε : ℝ} (hR : 0 < R)
    (u v : Sphere) (hc0 : -1 < c) (hc1 : c < 1)
    (hε : 0 ≤ ε) (hεR : ε ≤ 2*R) :
    capDisplacementLaw R u c (closedBall (R • (v : Space)) ε) ≤
      ENNReal.ofReal (ε^2 / (2*R^2*(1-c))) := by
  rw [capDisplacementLaw, Measure.map_apply (by fun_prop) isClosed_closedBall.measurableSet,
    displacement_ball_preimage hR hε]
  have hbound := capLaw_le_of_area_le u hc0 hc1 (measurableSet_cap v _)
    (area_chord_cap hR hε hεR v).le
  have he : (Real.pi*ε^2/R^2)/(2*Real.pi*(1-c)) = ε^2/(2*R^2*(1-c)) := by
    field_simp [Real.pi_ne_zero, hR.ne', (sub_pos.mpr hc1).ne']
    <;> ring
  rwa [he] at hbound
end QEC.Coding.ProbabilisticConstruction.SphericalCap

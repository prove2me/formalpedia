-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:11.110066+00:00
-- url     : https://prove2.me/submissions/f83c8819-97e2-47f7-8b59-e9ceb544f778

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cos_mem_open_unit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    area (cap u (Real.cos θ)) = ENNReal.ofReal (2*Real.pi*(1-Real.cos θ)) :=
  area_cap u (cos_mem_open_unit hθ0 hθπ).1 (cos_mem_open_unit hθ0 hθπ).2
end QEC.Coding.ProbabilisticConstruction.SphericalCap

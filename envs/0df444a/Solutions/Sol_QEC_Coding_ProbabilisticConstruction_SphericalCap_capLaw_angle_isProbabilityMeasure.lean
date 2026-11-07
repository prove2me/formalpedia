-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_angle_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:26.54503+00:00
-- url     : https://prove2.me/submissions/d2f1a98e-412b-46dd-bbb8-a9fd9e57cfaf

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cos_mem_open_unit
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_isProbabilityMeasure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : IsProbabilityMeasure (capLaw u (Real.cos θ)) :=
  capLaw_isProbabilityMeasure u (cos_mem_open_unit hθ0 hθπ).2
end QEC.Coding.ProbabilisticConstruction.SphericalCap

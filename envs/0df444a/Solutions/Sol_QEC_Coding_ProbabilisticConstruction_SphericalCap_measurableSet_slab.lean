-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_slab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:54.475781+00:00
-- url     : https://prove2.me/submissions/4213bab0-ff1c-4f0a-ad1c-63663431b163

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (n : Sphere) (d h : ℝ) : MeasurableSet (slab n d h) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap

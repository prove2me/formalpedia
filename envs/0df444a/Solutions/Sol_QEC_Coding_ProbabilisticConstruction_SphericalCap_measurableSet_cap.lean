-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:25.208605+00:00
-- url     : https://prove2.me/submissions/801ccae1-c730-44af-910a-bf0966fceb71

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_cap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) : MeasurableSet (cap u c) :=
  (isClosed_cap u c).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap

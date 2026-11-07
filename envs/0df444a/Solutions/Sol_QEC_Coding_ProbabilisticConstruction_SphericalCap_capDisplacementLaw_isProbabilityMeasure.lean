-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:09:35.470903+00:00
-- url     : https://prove2.me/submissions/980b3ce2-73fe-4740-a7b3-1d70eb922ec5

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_isProbabilityMeasure

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (R : ℝ) (u : Sphere) {c : ℝ}
    (hc : c < 1) : IsProbabilityMeasure (capDisplacementLaw R u c) := by
  letI := capLaw_isProbabilityMeasure u hc
  exact Measure.isProbabilityMeasure_map (by fun_prop)
end QEC.Coding.ProbabilisticConstruction.SphericalCap

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_displacementCap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:49.816611+00:00
-- url     : https://prove2.me/submissions/d558b617-44f9-4c40-8aa0-953a9d87554d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (R : ℝ) (u : Sphere) (c : ℝ) :
    MeasurableSet (displacementCap R u c) := by
  change MeasurableSet ({p : Space | ‖p‖ = R} ∩ {p : Space | R*c ≤ inner ℝ (u : Space) p})
  exact ((isClosed_eq continuous_norm continuous_const).inter
    (isClosed_le continuous_const (by fun_prop))).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap

-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:30.27191+00:00
-- url     : https://prove2.me/submissions/4480c9a5-8fa3-4165-bfd5-9912e5859851

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
theorem _root_.solution {R : ℝ} (hR : R ≠ 0) :
    Function.Injective (fun s : Sphere => R • (s : Space)) := by
  intro s t h
  apply Subtype.ext
  exact (smul_right_injective Space hR) h
end QEC.Coding.ProbabilisticConstruction.SphericalCap

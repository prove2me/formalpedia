-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axisReflection_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:07:54.896607+00:00
-- url     : https://prove2.me/submissions/227b05a7-df1c-475c-b757-c42e8b46c503

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u v : Ambient) :
    MeasurePreserving (axisReflection u v) volume volume :=
  (axisReflection u v).measurePreserving
end QEC.Coding.ProbabilisticConstruction.SphericalCap

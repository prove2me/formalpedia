-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axisReflection_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:55:20.889196+00:00
-- url     : https://prove2.me/submissions/6caf63c2-6dd0-4647-8106-7966d5e68e2e

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u v : Ambient) (h : ‖u‖ = ‖v‖) :
    axisReflection u v u = v := Submodule.reflection_sub h
end QEC.Coding.ProbabilisticConstruction.SphericalCap

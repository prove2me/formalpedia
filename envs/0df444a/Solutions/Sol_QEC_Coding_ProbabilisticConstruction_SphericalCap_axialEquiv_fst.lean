-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:46.293067+00:00
-- url     : https://prove2.me/submissions/36245814-5f2f-4ca3-940f-dda4fd60353c

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (x : Ambient) : (axialEquiv x).1 = x 0 := rfl
end QEC.Coding.ProbabilisticConstruction.SphericalCap

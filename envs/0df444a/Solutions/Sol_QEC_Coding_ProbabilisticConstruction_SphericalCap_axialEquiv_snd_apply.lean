-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:02.630951+00:00
-- url     : https://prove2.me/submissions/a4247be8-ad3a-4f47-89c5-9d3d836f675c

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (x : Ambient) (i : Fin 2) :
    (axialEquiv x).2 i = x i.succ := rfl
end QEC.Coding.ProbabilisticConstruction.SphericalCap

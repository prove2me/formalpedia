-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:21.681027+00:00
-- url     : https://prove2.me/submissions/24d94786-d8bd-4e4a-a929-6348f63de3b4

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution :
    MeasurePreserving axialEquiv volume (volume.prod volume) := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))
end QEC.Coding.ProbabilisticConstruction.SphericalCap

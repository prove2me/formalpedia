-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.norm_sq_axial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:53.794236+00:00
-- url     : https://prove2.me/submissions/9a42f620-61a1-4689-ac90-50aaaedc9ec0

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (x : Ambient) :
    ‖x‖ ^ 2 = (axialEquiv x).1 ^ 2 + ‖(axialEquiv x).2‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    axialEquiv_fst, axialEquiv_snd_apply]
end QEC.Coding.ProbabilisticConstruction.SphericalCap

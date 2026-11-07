-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:08:30.031904+00:00
-- url     : https://prove2.me/submissions/d6e4a37a-eb2b-401c-950d-e2e5e64ce1ad

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (a : Fin 3 → Space) (w : Fin 3 → ℝ) :
    barycenterMap a w = ∑ i, w i • a i := by simp [barycenterMap]
end QEC.Coding.ProbabilisticConstruction.SphericalCap

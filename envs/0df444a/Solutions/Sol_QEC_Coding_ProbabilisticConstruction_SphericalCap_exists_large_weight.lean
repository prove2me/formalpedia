-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_large_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:43.223311+00:00
-- url     : https://prove2.me/submissions/a54f8614-16d5-4fa9-84c6-4a059a8f2f7e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {w : Fin 3 → ℝ} (hw : w ∈ stdSimplex ℝ (Fin 3)) :
    ∃ i, (1:ℝ)/3 ≤ w i := by
  by_contra! h
  have hs := hw.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change w 0 + (w 1 + w 2) = 1 at hs
  linarith [h 0, h 1, h 2]
end QEC.Coding.ProbabilisticConstruction.SphericalCap

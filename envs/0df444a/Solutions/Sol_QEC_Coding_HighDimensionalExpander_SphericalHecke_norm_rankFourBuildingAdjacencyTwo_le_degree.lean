-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_rankFourBuildingAdjacencyTwo_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:16.006539+00:00
-- url     : https://prove2.me/submissions/aefcf167-c8c4-4a30-80ef-01ff6b2f7262

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_norm_buildingColoredAdjacencyOperatorOfInv_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_two_inv


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] :
    ‖rankFourBuildingAdjacencyTwo k‖ ≤
      coloredAdjacencyDegree k 4 2 := by
  calc
    ‖rankFourBuildingAdjacencyTwo k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 4 2 : ℝ) *
          coloredAdjacencyDegree k 4 2) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 4 2 2
        (fundamentalDoubleCoset_rankFour_two_inv k)
    _ = coloredAdjacencyDegree k 4 2 := by
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
end QEC.Coding.HighDimensionalExpander.SphericalHecke

-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_rankFourBuildingAdjacencyOne_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:13.356029+00:00
-- url     : https://prove2.me/submissions/fdd772bb-e8f2-448d-ac02-037fcf8a10a9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_norm_buildingColoredAdjacencyOperatorOfInv_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_one_inv


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] :
    ‖rankFourBuildingAdjacencyOne k‖ ≤
      coloredAdjacencyDegree k 4 1 := by
  calc
    ‖rankFourBuildingAdjacencyOne k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 4 1 : ℝ) *
          coloredAdjacencyDegree k 4 3) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 4 1 3
        (fundamentalDoubleCoset_rankFour_one_inv k)
    _ = coloredAdjacencyDegree k 4 1 := by
      rw [coloredAdjacencyDegree_rankFour_one,
        coloredAdjacencyDegree_rankFour_three]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
end QEC.Coding.HighDimensionalExpander.SphericalHecke

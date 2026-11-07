-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:56:58.764209+00:00
-- url     : https://prove2.me/submissions/961689ca-64b6-4145-832e-4bdecc31c146

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_buildingColoredAdjacencyOperatorOfInv
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
    (rankFourBuildingAdjacencyTwo k)† =
      rankFourBuildingAdjacencyTwo k :=
  adjoint_buildingColoredAdjacencyOperatorOfInv k 4 2 2
    (fundamentalDoubleCoset_rankFour_two_inv k)
    (fundamentalDoubleCoset_rankFour_two_inv k)
end QEC.Coding.HighDimensionalExpander.SphericalHecke

-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.isClosed_rankThreeBuildingJointApproximateSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:38.851117+00:00
-- url     : https://prove2.me/submissions/23469a46-dd69-48d5-b77c-de8bb50063d0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isClosed_jointApproximatePointSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] :
    IsClosed (RankThreeBuildingJointApproximateSpectrum k) :=
  isClosed_jointApproximatePointSpectrum
    (rankThreeBuildingAdjacencyFamily k)
end QEC.Coding.HighDimensionalExpander.SphericalHecke

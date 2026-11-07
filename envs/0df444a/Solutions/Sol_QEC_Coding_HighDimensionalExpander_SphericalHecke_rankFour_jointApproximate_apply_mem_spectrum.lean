-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_jointApproximate_apply_mem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:07:32.970214+00:00
-- url     : https://prove2.me/submissions/841f379f-f8b6-4989-a1f5-d5cf5da2749d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_apply_mem_spectrum_of_mem_jointApproximatePointSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k]
    (a : Fin 3 → ℂ) (ha : a ∈ RankFourBuildingJointApproximateSpectrum k)
    (color : Fin 3) :
    a color ∈ spectrum ℂ (rankFourBuildingAdjacencyFamily k color) :=
  apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
    (rankFourBuildingAdjacencyFamily k) a ha color
end QEC.Coding.HighDimensionalExpander.SphericalHecke

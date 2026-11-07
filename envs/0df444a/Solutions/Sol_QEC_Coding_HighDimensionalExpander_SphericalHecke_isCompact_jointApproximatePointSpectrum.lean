-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.isCompact_jointApproximatePointSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:25:03.339059+00:00
-- url     : https://prove2.me/submissions/aee2c4bb-5b0c-411f-be25-431b1af5acf0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isClosed_jointApproximatePointSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isBounded_jointApproximatePointSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) :
    IsCompact (jointApproximatePointSpectrum A) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_jointApproximatePointSpectrum A)
    (isBounded_jointApproximatePointSpectrum A)
end QEC.Coding.HighDimensionalExpander.SphericalHecke

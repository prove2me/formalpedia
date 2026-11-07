-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.mem_jointApproximatePointSpectrum_of_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:37.705652+00:00
-- url     : https://prove2.me/submissions/75753314-43d6-48e0-9a17-de7b87b50fa9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ) (v : E)
    (hv : ‖v‖ = 1) (heigen : ∀ i, A i v = a i • v) :
    a ∈ jointApproximatePointSpectrum A := by
  intro ε hε
  refine ⟨v, hv, ?_⟩
  intro i
  rw [heigen i, sub_self, norm_zero]
  exact hε
end QEC.Coding.HighDimensionalExpander.SphericalHecke

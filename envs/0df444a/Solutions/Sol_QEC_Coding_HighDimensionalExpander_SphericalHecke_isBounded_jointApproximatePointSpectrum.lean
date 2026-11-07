-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.isBounded_jointApproximatePointSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:23:40.169713+00:00
-- url     : https://prove2.me/submissions/540d11fc-6c05-483e-8d81-5428e64ae5da

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_norm_apply_le_of_mem_jointApproximatePointSpectrum

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
    Bornology.IsBounded (jointApproximatePointSpectrum A) := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : ι → ℂ)).2
  refine ⟨∑ i : ι, ‖A i‖, ?_⟩
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
  intro i
  exact (norm_apply_le_of_mem_jointApproximatePointSpectrum A a ha i).trans
    (Finset.single_le_sum (fun j _ ↦ norm_nonneg (A j))
      (Finset.mem_univ i))
end QEC.Coding.HighDimensionalExpander.SphericalHecke

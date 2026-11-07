-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_dimensions_and_distances_of_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:02:25.51454+00:00
-- url     : https://prove2.me/submissions/33e32187-0189-4653-90f8-bdabd6d9455c

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_iff_exists
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
import Theorems.Thm_QEC_Coding_QuantumTanner_dimensions_of_fullRowRank

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      2 * (2 ^ r - 1) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
          2 * (((2 ^ r - 1) *
              (∑ weight ∈ Finset.range distance,
                Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) *
            (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        Dimension sample.codeA = r ∧
          Dimension sample.codeB = Delta - r ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  rw [hasPositiveUniformProbability_iff_exists]
  obtain ⟨sample, hFull, hDistanceA, hDistanceB,
    hDistanceADual, hDistanceBDual⟩ :=
    (hasPositiveUniformProbability_iff_exists _).mp
      (hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
        hA hB hcount)
  obtain ⟨hDimensionA, hDimensionB⟩ :=
    dimensions_of_fullRowRank sample hA hB hFull
  exact ⟨sample, hDimensionA, hDimensionB, hDistanceA, hDistanceB,
    hDistanceADual, hDistanceBDual⟩
end QEC.Coding.QuantumTanner

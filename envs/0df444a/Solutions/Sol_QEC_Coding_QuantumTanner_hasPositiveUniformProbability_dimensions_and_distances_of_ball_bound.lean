-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_dimensions_and_distances_of_ball_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:40:04.433223+00:00
-- url     : https://prove2.me/submissions/ecf2ef1e-3eac-4941-9c72-b1e7467d84fa

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
import Theorems.Thm_QEC_Coding_QuantumTanner_simultaneousDistance_count_bound_of_ball_bound
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_dimensions_and_distances_of_count_bound

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
    (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hball :
      2 * (2 ^ r - 1) +
          2 * ((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        Dimension sample.codeA = r ∧
          Dimension sample.codeB = Delta - r ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) :=
  hasPositiveUniformProbability_dimensions_and_distances_of_count_bound
    hA hB (simultaneousDistance_count_bound_of_ball_bound hr hrDelta hball)
end QEC.Coding.QuantumTanner

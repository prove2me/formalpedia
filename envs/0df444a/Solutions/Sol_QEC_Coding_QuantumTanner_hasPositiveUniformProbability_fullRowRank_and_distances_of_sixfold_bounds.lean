-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_fullRowRank_and_distances_of_sixfold_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:01:43.437882+00:00
-- url     : https://prove2.me/submissions/d777dde5-683c-489b-abf4-983c6e58b1b7

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
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
section
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
section RobustnessAsymptotics
open Filter
end RobustnessAsymptotics
section RobustnessIndexBounds
open Filter
end RobustnessIndexBounds
private theorem simultaneousDistance_ball_bound_of_sixfold_components
    {r Delta distance : Nat}
    (hRank : 6 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      6 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      6 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) < 2 ^ Delta) :
    2 * (2 ^ r - 1) +
        2 * ((2 ^ r - 1) *
          (∑ weight ∈ Finset.range distance,
            Nat.choose Delta weight)) +
        2 * ((∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight) * 2 ^ (Delta - r)) <
      2 ^ Delta := by
  omega
namespace ChainComplexData
end ChainComplexData
namespace LeftRightCayleySquareComplex
end LeftRightCayleySquareComplex
namespace RawData
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
end RawData
namespace Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
variable [DecidableEq Square]
end Data
namespace Family
variable {Index : Type u}
variable {G A B Square XBasis ZBasis : Index → Type v}
variable [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable [∀ i, Fintype (Square i)] [∀ i, DecidableEq (Square i)]
variable [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
end Family
end QEC.Coding.QuantumTanner
end
end

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
    (hRank : 6 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      6 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      6 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) < 2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  apply hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
    hA hB
  exact simultaneousDistance_count_bound_of_ball_bound hr hrDelta
    (simultaneousDistance_ball_bound_of_sixfold_components
      hRank hGenerator hKernel)
end QEC.Coding.QuantumTanner

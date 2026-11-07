-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.goodLocalCodeEvent_of_fullRowRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:04:02.923224+00:00
-- url     : https://prove2.me/submissions/2dcc6732-4ef4-43a1-8159-724de1cc007d

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
import Theorems.Thm_QEC_Coding_QuantumTanner_dimensions_of_fullRowRank

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {r Delta distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hFull : sample.HasFullRowRank)
    (hDistanceA : HasMinimumDistanceAtLeast sample.codeA distanceThreshold)
    (hDistanceB : HasMinimumDistanceAtLeast sample.codeB distanceThreshold)
    (hDistanceADual :
      HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold)
    (hDistanceBDual :
      HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold)
    (hRobust : IsRobustWithPunctureResistance
      sample.codeA sample.codeB robustness punctures)
    (hRobustDual : IsRobustWithPunctureResistance
      sample.codeA.dual sample.codeB.dual robustness punctures) :
    GoodLocalCodeEvent
      r (Delta - r) distanceThreshold robustness punctures sample := by
  obtain ⟨hDimensionA, hDimensionB⟩ :=
    dimensions_of_fullRowRank sample hA hB hFull
  exact ⟨hDimensionA, hDimensionB, hDistanceA, hDistanceB,
    hDistanceADual, hDistanceBDual, hRobust, hRobustDual⟩
end QEC.Coding.QuantumTanner

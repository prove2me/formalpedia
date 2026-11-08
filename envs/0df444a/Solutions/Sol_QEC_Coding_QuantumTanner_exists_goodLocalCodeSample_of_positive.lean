-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_goodLocalCodeSample_of_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:40:17.114875+00:00
-- url     : https://prove2.me/submissions/cb171745-8e18-45f0-8651-3332c9d10079

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

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {r dimensionA dimensionB distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    [DecidablePred (GoodLocalCodeEvent
      (r := r) (A := A) (B := B)
      dimensionA dimensionB distanceThreshold robustness punctures)]
    (hpositive : HasPositiveUniformProbability
      (GoodLocalCodeEvent
        (r := r) (A := A) (B := B)
        dimensionA dimensionB distanceThreshold robustness punctures)) :
    ∃ sample : RandomLocalCodeSample r A B,
      GoodLocalCodeEvent
        dimensionA dimensionB distanceThreshold robustness punctures sample := by
  exact (hasPositiveUniformProbability_iff_exists _).mp hpositive
end QEC.Coding.QuantumTanner

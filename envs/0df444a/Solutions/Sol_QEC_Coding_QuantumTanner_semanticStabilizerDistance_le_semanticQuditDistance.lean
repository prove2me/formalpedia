-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_semanticQuditDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:03:14.669182+00:00
-- url     : https://prove2.me/submissions/aeb1081d-933a-45c5-88bb-356394750e95

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
import Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
import Theorems.Thm_QEC_Coding_QuantumTanner_semanticQuditDistance_logicalRegions_nonempty

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : iota => 2) Q.1.code :=
  semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
    Q hDistance (semanticQuditDistance_logicalRegions_nonempty Q hDistance)
end QEC.Coding.QuantumTanner

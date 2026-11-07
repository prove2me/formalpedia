-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Dimension_tensorCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:33:02.209017+00:00
-- url     : https://prove2.me/submissions/5fedbe20-9366-490d-8e00-d89b4526bd43

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

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Dimension (tensorCode CA CB) = Dimension CA * Dimension CB := by
  rw [Dimension_eq_finrank_carrier,
    ← (tensorCodeTensorEquiv CA CB).finrank_eq,
    Module.finrank_tensorProduct,
    ← Dimension_eq_finrank_carrier,
    ← Dimension_eq_finrank_carrier]
end QEC.Coding.QuantumTanner

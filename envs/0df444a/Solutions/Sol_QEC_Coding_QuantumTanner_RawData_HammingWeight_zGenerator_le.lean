-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.RawData.HammingWeight_zGenerator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:47:51.209943+00:00
-- url     : https://prove2.me/submissions/94eb2753-dce2-4e2e-9eb9-ca30a006b93a

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
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_HammingWeight_localExtension_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
open QEC.Coding.QuantumTanner.RawData
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.RawData
theorem _root_.solution
    (D : RawData G A B Square XBasis ZBasis) (check : G × ZBasis) :
    HammingWeight (D.zGenerator check) ≤
      Fintype.card A * Fintype.card B := by
  exact D.complex.HammingWeight_localExtension_le
    (check.1, false) (D.zBasis check.2).1
end QEC.Coding.QuantumTanner.RawData

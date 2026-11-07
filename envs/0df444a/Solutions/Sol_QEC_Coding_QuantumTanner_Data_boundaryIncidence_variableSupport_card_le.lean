-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.boundaryIncidence_variableSupport_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:07:58.229753+00:00
-- url     : https://prove2.me/submissions/aa66c35e-1e58-433d-a735-ee90d59bc8e3

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
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_HammingWeight_boundary1_basis_le
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_HammingWeight_transpose_boundary2_basis_le
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) (square : Square) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).variableSupport
      square).card ≤
        2 * Fintype.card XBasis + 2 * Fintype.card ZBasis := by
  rw [QEC.QLDPC.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns]
  exact Nat.add_le_add
    (D.toRawData.HammingWeight_boundary1_basis_le square)
    (D.toRawData.HammingWeight_transpose_boundary2_basis_le square)
end QEC.Coding.QuantumTanner.Data

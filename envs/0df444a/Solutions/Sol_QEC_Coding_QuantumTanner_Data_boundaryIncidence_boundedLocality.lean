-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.boundaryIncidence_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:03:36.481102+00:00
-- url     : https://prove2.me/submissions/759e6713-8ae6-4e4d-abd4-19048124a3da

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
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_HammingWeight_xGenerator_le
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_HammingWeight_zGenerator_le
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_variableSupport_card_le
import Theorems.Thm_QEC_Coding_wordLinearMapTranspose_transpose
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds


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
    (D : Data G A B Square XBasis ZBasis) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (max (Fintype.card A * Fintype.card B)
        (2 * Fintype.card XBasis + 2 * Fintype.card ZBasis)) := by
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
  · intro check
    change HammingWeight
      (wordLinearMapTranspose D.toRawData.boundary1
        (canonicalBasisWord (F := ZMod 2) check)) ≤ _
    rw [RawData.boundary1,
      wordLinearMapTranspose_transpose, RawData.xGeneratorMap,
      RawData.linearMapOfGenerators_canonicalBasis]
    exact D.toRawData.HammingWeight_xGenerator_le check
  · intro check
    change HammingWeight
      (D.toRawData.boundary2
        (canonicalBasisWord (F := ZMod 2) check)) ≤ _
    rw [RawData.boundary2, RawData.zGeneratorMap,
      RawData.linearMapOfGenerators_canonicalBasis]
    exact D.toRawData.HammingWeight_zGenerator_le check
  · exact D.boundaryIncidence_variableSupport_card_le
end QEC.Coding.QuantumTanner.Data

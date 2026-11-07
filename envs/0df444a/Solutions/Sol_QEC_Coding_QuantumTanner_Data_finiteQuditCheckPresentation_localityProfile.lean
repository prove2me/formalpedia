-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.finiteQuditCheckPresentation_localityProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:04:58.294871+00:00
-- url     : https://prove2.me/submissions/eec59d77-296b-40fc-ba74-e25ea4279510

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
import Theorems.Thm_QEC_Coding_QuantumTanner_ChainComplexData_finiteQuditCheckPresentation_localityProfile

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
variable [DecidableEq Square]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile := by
  exact ChainComplexData.finiteQuditCheckPresentation_localityProfile
    D.chainComplex D.encodedDimension
      D.finrank_binaryCSSCode_carrier_eq_pow_encodedDimension
end QEC.Coding.QuantumTanner.Data

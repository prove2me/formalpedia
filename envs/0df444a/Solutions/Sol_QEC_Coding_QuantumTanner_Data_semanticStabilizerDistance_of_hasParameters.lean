-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.semanticStabilizerDistance_of_hasParameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:46:32.095448+00:00
-- url     : https://prove2.me/submissions/a1f4a99f-f4c2-4603-b74e-9177dd0b5bf3

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
import Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_of_algebraicCSSMinimumDistance
import Theorems.Thm_QEC_Coding_QuantumTanner_ChainComplexData_semanticStabilizerDistance_of_algebraicCSSMinimumDistance

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
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    StabilizerCode.SemanticStabilizerDistance
      D.chainComplex.binaryCSSSourceValidStabilizer distance :=
  ChainComplexData.semanticStabilizerDistance_of_algebraicCSSMinimumDistance
    D.chainComplex hParameters.2.2
end QEC.Coding.QuantumTanner.Data

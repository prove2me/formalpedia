-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.randomRowCount_lt_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:33:51.511326+00:00
-- url     : https://prove2.me/submissions/a5a2ae4c-1187-49ce-acca-0d8825835965

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
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_cast_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {rho : ℝ} {Delta : Nat} (hRhoNonnegative : 0 ≤ rho)
    (hRhoOne : rho < 1) (hDelta : 0 < Delta) :
    randomRowCount rho Delta < Delta := by
  have hDeltaReal : 0 < (Delta : ℝ) := by
    exact_mod_cast hDelta
  have hRowsReal : (randomRowCount rho Delta : ℝ) ≤ rho * Delta :=
    randomRowCount_cast_le hRhoNonnegative
  have hProduct : rho * (Delta : ℝ) < Delta := by
    nlinarith
  exact_mod_cast hRowsReal.trans_lt hProduct
end QEC.Coding.QuantumTanner

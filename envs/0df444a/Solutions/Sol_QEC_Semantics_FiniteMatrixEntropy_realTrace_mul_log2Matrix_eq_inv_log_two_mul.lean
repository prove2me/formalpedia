-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:54:52.702726+00:00
-- url     : https://prove2.me/submissions/05ccfaad-8a80-4098-8406-394160af2351

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_real_smul
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_eq_inv_log_two_smul_logMatrix

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    realTrace (A * log2Matrix A hA) =
      (Real.log 2)⁻¹ * realTrace (A * logMatrix A hA) := by
  rw [log2Matrix_eq_inv_log_two_smul_logMatrix]
  rw [Matrix.mul_smul, realTrace_real_smul]
end QEC.Semantics.FiniteMatrixEntropy

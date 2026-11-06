-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.log2Matrix_eq_inv_log_two_smul_logMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:52:36.018761+00:00
-- url     : https://prove2.me/submissions/3c255253-3423-4ec5-ad17-75a04c87f1fe

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply



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
    log2Matrix A hA = (Real.log 2)⁻¹ • logMatrix A hA := by
  rw [log2Matrix_apply, logMatrix_apply, ← hA.cfc_eq]
  rw [← hA.cfc_eq Real.log]
  have hcont : ContinuousOn Real.log (spectrum Real A) :=
    Matrix.finite_real_spectrum.continuousOn Real.log
  rw [← cfc_smul (p := IsSelfAdjoint) (Real.log 2)⁻¹ Real.log A hcont]
  congr 1
  funext x
  rw [Real.logb, div_eq_mul_inv]
  ring
end QEC.Semantics.FiniteMatrixEntropy

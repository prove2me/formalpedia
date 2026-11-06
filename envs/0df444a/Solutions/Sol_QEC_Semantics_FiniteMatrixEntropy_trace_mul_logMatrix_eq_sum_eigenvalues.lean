-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_eq_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:43:11.29967+00:00
-- url     : https://prove2.me/submissions/c2a850c2-015c-40d1-9669-05c895176975

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_cfc_eq_sum_eigenvalues

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    (A * logMatrix A hA).trace =
      (∑ i, (hA.eigenvalues i * Real.log (hA.eigenvalues i) : Real) : Complex) := by
  exact trace_mul_cfc_eq_sum_eigenvalues A hA Real.log
end QEC.Semantics.FiniteMatrixEntropy

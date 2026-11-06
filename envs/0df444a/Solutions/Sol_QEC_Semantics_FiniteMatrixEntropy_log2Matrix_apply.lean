-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:38:40.995315+00:00
-- url     : https://prove2.me/submissions/e1e8cb5d-6c74-47eb-b8f0-fefe0c8cb6c2

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative

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
    log2Matrix A hA = hA.cfc (Real.logb 2) :=
  rfl
end QEC.Semantics.FiniteMatrixEntropy

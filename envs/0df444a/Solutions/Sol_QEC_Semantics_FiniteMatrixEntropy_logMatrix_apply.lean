-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:38:52.282891+00:00
-- url     : https://prove2.me/submissions/6aba5433-2305-43df-a294-4d025af010db

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
    logMatrix A hA = hA.cfc Real.log :=
  rfl
end QEC.Semantics.FiniteMatrixEntropy

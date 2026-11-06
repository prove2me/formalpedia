-- Prove2me | solution 1 for QEC.Semantics.Qubit.localX_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:42:54.952388+00:00
-- url     : https://prove2.me/submissions/7430af45-0ae5-48cf-8caa-e89289194dc1

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localXMatrix_conjTranspose

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (i : ι) : LinearMap.adjoint (localX i) = localX i := by
  classical
  change LinearMap.adjoint (Matrix.toEuclideanLin (localXMatrix i)) =
    Matrix.toEuclideanLin (localXMatrix i)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint (localXMatrix i),
    localXMatrix_conjTranspose]
end QEC.Semantics.Qubit

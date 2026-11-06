-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZ_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:42:42.547871+00:00
-- url     : https://prove2.me/submissions/62307186-965f-4806-92ef-a601da9da74d

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localZMatrix_conjTranspose

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
theorem _root_.solution (i : ι) : LinearMap.adjoint (localZ i) = localZ i := by
  classical
  change LinearMap.adjoint (Matrix.toEuclideanLin (localZMatrix i)) =
    Matrix.toEuclideanLin (localZMatrix i)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint (localZMatrix i),
    localZMatrix_conjTranspose]
end QEC.Semantics.Qubit

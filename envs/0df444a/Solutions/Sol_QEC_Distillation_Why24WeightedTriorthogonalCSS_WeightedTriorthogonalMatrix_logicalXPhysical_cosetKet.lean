-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalXPhysical_cosetKet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:10:02.672374+00:00
-- url     : https://prove2.me/submissions/460db5e1-f96d-42ab-ad82-d526d9a6a350

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalWord_add
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_wordXTransport_apply_basis
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalWord_logicalBasisWord

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]
namespace QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
theorem _root_.solution
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) (u : Logical → F1024) :
    R.logicalXPhysical a beta (R.cosetKet u) =
      R.cosetKet (u + logicalBasisWord a beta) := by
  unfold logicalXPhysical cosetKet
  rw [map_smul, map_sum]
  simp_rw [wordXTransport_apply_basis]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  unfold cosetLabel
  rw [R.logicalWord_add, R.logicalWord_logicalBasisWord]
  abel
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix

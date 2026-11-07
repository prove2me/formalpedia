-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalXPhysical_intertwines_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:12:35.587559+00:00
-- url     : https://prove2.me/submissions/4fa2ecae-3f8c-40c0-a5ea-ddce116cb994

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_wordXTransport_apply_basis
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalXPhysical_cosetKet

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
    R.logicalXPhysical a beta
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalXLogical a beta (registerBasisKet u)) := by
  rw [R.encodedCode_apply_logical_basis, R.logicalXPhysical_cosetKet]
  unfold logicalXLogical
  rw [wordXTransport_apply_basis, R.encodedCode_apply_logical_basis]
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix

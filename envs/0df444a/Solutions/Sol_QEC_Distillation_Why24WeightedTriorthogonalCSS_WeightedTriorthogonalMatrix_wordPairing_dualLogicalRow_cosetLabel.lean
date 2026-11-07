-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.wordPairing_dualLogicalRow_cosetLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:13:03.241624+00:00
-- url     : https://prove2.me/submissions/8d2a5067-6f72-4782-92f1-b532e28fdef7

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_dualLogicalRow_mem_stabilizerCode_dual
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalWord_dualLogicalRow_pairing

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
    (u : Logical → F1024) (h : R.StabilizerCarrier) (a : Logical) :
    wordPairing (R.dualLogicalRow a) (R.cosetLabel u h) = u a := by
  unfold cosetLabel
  rw [(wordPairing (R.dualLogicalRow a)).map_add]
  have hlogical : wordPairing (R.dualLogicalRow a) (R.logicalWord u) = u a := by
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
    exact R.logicalWord_dualLogicalRow_pairing u a
  have hstabilizer : wordPairing (R.dualLogicalRow a) (h : Why24Word Site) = 0 :=
    R.stabilizerCode.orthogonal_of_mem_dual
      (R.dualLogicalRow_mem_stabilizerCode_dual a) h.property
  rw [hlogical, hstabilizer, add_zero]
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_apply_tmul_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:02:24.852323+00:00
-- url     : https://prove2.me/submissions/ee8619a6-da29-48c7-9cd7-792951de3823

import Definitions.Def_QEC_Import_Compact_f7cc1b973e83a32c
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_apply_tmul_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_apply_tmul_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «ccomponent» «nC» «compact_inst_7» «WC» «UC» «x» «n» «d»
  rfl
end QEC.Bounds.BPTCommutingProjectorModel

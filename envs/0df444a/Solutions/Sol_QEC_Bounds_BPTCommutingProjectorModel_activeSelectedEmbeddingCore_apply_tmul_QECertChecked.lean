-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeSelectedEmbeddingCore_apply_tmul_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:02:41.777017+00:00
-- url     : https://prove2.me/submissions/4f3bf396-b9b0-48a1-83bb-8d2264b70404

import Definitions.Def_QEC_Import_Compact_ba2f0537c0540e55
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore

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
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.activeSelectedEmbeddingCore_apply_tmul_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.activeSelectedEmbeddingCore_apply_tmul_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «bcomponent» «nB» «compact_inst_7» «WB» «UB» «a» «w» «n»
  rfl
end QEC.Bounds.BPTCommutingProjectorModel

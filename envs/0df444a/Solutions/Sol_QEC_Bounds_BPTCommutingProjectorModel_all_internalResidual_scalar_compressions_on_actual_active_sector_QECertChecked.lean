-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.all_internalResidual_scalar_compressions_on_actual_active_sector_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:12:27.579124+00:00
-- url     : https://prove2.me/submissions/90145629-5de0-4b71-b10b-d4199c3fd45a

import Definitions.Def_QEC_Import_Compact_4cdbe99c34b948a0
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalAssembly
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_internalResidual_scalar_compression_on_actual_active_sector_QECertChecked


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.all_internalResidual_scalar_compressions_on_actual_active_sector_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.all_internalResidual_scalar_compressions_on_actual_active_sector_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «ccomponent» «nC» «nB» «compact_inst_8» «compact_inst_9» «WC» «UC» «Qsecond» «hQ» «hsupport» «hphysical»
  intro X
  rcases hphysical X with ⟨scalar, hscalar⟩
  refine ⟨scalar, ?_⟩
  exact M.internalResidual_scalar_compression_on_actual_active_sector_QECertChecked
    region ccomponent WC UC Qsecond X scalar hQ hsupport hscalar
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.all_externalResidual_scalar_compressions_on_actual_active_sector_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:12:30.97174+00:00
-- url     : https://prove2.me/submissions/1ce93038-83f1-4bf5-a54c-85b94700b346

import Definitions.Def_QEC_Import_Compact_b94046e01f65d82c
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalAssembly
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalResidual_scalar_compression_on_actual_active_sector_QECertChecked


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
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.all_externalResidual_scalar_compressions_on_actual_active_sector_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.all_externalResidual_scalar_compressions_on_actual_active_sector_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «ccomponent» «nC» «nB» «compact_inst_8» «compact_inst_9» «WC» «UC» «Qsecond» «hQ» «hsupport» «hphysical»
  intro Y
  rcases hphysical Y with ⟨E, Ephysical, scalar, hPullback, hscalar⟩
  refine ⟨scalar, ?_⟩
  exact M.externalResidual_scalar_compression_on_actual_active_sector_QECertChecked
    region ccomponent WC UC Qsecond Y E Ephysical scalar hPullback hQ hsupport hscalar
end QEC.Bounds.BPTCommutingProjectorModel

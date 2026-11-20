-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_compressed_overlap_product_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:12:17.67697+00:00
-- url     : https://prove2.me/submissions/9cf86a58-306d-4f29-bbe8-35093995d7e4

import Definitions.Def_QEC_Import_Compact_a452780b876c8709
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_overlap_product
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_compression_overlap_product_eq_sector_block_product_QECertChecked


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
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_compressed_overlap_product_QECertStatement.{u} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_compressed_overlap_product_QECertStatement
  intro «A» «H» «W» «N» «C» «compact_inst_5» «compact_inst_6» «compact_inst_7» «compact_inst_8» «compact_inst_9» «compact_inst_10» «compact_inst_11» «compact_inst_12» «compact_inst_13» «compact_inst_14» «compact_inst_15» «compact_inst_16» «compact_inst_17» «compact_inst_18» «compact_inst_19» «P» «Q» «hselfAdjoint» «hcommute» «component» «U» «Pleft» «Qright» «hleft» «hright»
  rw [isotypic_compression_overlap_product_eq_sector_block_product_QECertChecked
    P Q hselfAdjoint hcommute component]
  exact isotypicSectorBlockTransportLeft_conj_overlap_product U
    (overlapProjectorOnIsotypicComponent P component)
    (overlapRightProjectorOnIsotypicComponent P Q component)
    Pleft Qright hleft hright
end QEC.Bounds.BPTCommutingProjectorModel

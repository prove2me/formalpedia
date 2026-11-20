-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:02:20.497835+00:00
-- url     : https://prove2.me/submissions/4a30d4f0-5e35-43b4-b4b8-ada67d6dc0cb

import Definitions.Def_QEC_Import_Compact_58ab7efebc15ad33
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutFactorizedCompression_eq_sequential_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_congr_of_embedding_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionLeft_eq_sequentialFirstCutCompression_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «pB» «pC»
  have hJ := M.jointBCSectorEmbeddingLeft_eq_firstCutSector_after_secondCutSector
    region pB pC
  calc
    (LinearMap.adjoint
      (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.firstCutCodeLift region).comp
        (jointBCSectorEmbeddingLeft (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      (LinearMap.adjoint ((M.firstCutSelectedCEmbedding region pC).comp
        (M.firstCutSelectedBAfterCEmbedding region pB pC))).comp
        ((M.firstCutCodeLift region).comp
          ((M.firstCutSelectedCEmbedding region pC).comp
            (M.firstCutSelectedBAfterCEmbedding region pB pC))) :=
        compression_congr_of_embedding_eq (M.firstCutCodeLift region) hJ
    _ = _ := M.firstCutFactorizedCompression_eq_sequential_QECertChecked region pB pC
end QEC.Bounds.BPTCommutingProjectorModel

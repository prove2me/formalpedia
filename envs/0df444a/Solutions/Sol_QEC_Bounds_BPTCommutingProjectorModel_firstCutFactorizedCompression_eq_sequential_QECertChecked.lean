-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutFactorizedCompression_eq_sequential_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:59:07.05192+00:00
-- url     : https://prove2.me/submissions/00f46cdd-8a59-4737-be47-7411a4458255

import Definitions.Def_QEC_Import_Compact_45bd38e38242d773
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_comp_embedding


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.QEC.QECertImportCore.proof_45bd38e38242d773
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.firstCutSelectedCEmbedding region pC).comp
      (M.firstCutSelectedBAfterCEmbedding region pB pC))).comp
      ((M.firstCutCodeLift region).comp
        ((M.firstCutSelectedCEmbedding region pC).comp
          (M.firstCutSelectedBAfterCEmbedding region pB pC))) =
      M.sequentialFirstCutJointCompression region pB pC := by
  exact compression_comp_embedding
    (M.firstCutSelectedCEmbedding region pC)
    (M.firstCutSelectedBAfterCEmbedding region pB pC)
    (M.firstCutCodeLift region)
end QEC.Bounds.BPTCommutingProjectorModel

end

universe checked_u0
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.firstCutFactorizedCompression_eq_sequential_QECertStatement.{checked_u0} := @QEC.QECertImportCore.proof_45bd38e38242d773.{checked_u0}

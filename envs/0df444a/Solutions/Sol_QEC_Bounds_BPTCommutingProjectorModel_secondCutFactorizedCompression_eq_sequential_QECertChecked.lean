-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutFactorizedCompression_eq_sequential_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:59:05.748204+00:00
-- url     : https://prove2.me/submissions/35e15cf7-5902-4e4c-84c5-941a307e03c6

import Definitions.Def_QEC_Import_Compact_5fad1f5e448917cb
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
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
theorem _root_.QEC.QECertImportCore.proof_5fad1f5e448917cb
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
      (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
      ((M.secondCutCodeLift region).comp
        ((M.secondCutSelectedBEmbedding region pB).comp
          (M.secondCutSelectedCAfterBEmbedding region pB pC))) =
      M.sequentialSecondCutJointCompression region pB pC := by
  exact compression_comp_embedding
    (M.secondCutSelectedBEmbedding region pB)
    (M.secondCutSelectedCAfterBEmbedding region pB pC)
    (M.secondCutCodeLift region)
end QEC.Bounds.BPTCommutingProjectorModel

end

universe checked_u0
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCutFactorizedCompression_eq_sequential_QECertStatement.{checked_u0} := @QEC.QECertImportCore.proof_5fad1f5e448917cb.{checked_u0}

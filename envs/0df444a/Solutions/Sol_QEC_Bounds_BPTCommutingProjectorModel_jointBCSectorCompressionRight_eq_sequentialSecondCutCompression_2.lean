-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:14.214776+00:00
-- url     : https://prove2.me/submissions/88acfd32-7c29-4e9f-8f73-df4a072ec681

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_congr_of_embedding_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutFactorizedCompression_eq_sequential_QECertChecked

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
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    M.secondCutJointCompression region pB pC =
      M.sequentialSecondCutJointCompression region pB pC := by
  unfold secondCutJointCompression
  have hJ := M.jointBCSectorEmbeddingRight_eq_secondCutSector_then_firstCutSector
    region pB pC
  calc
    (LinearMap.adjoint
      (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.secondCutCodeLift region).comp
        (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
        (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
        ((M.secondCutCodeLift region).comp
          ((M.secondCutSelectedBEmbedding region pB).comp
            (M.secondCutSelectedCAfterBEmbedding region pB pC))) :=
        compression_congr_of_embedding_eq (M.secondCutCodeLift region) hJ
    _ = _ := M.secondCutFactorizedCompression_eq_sequential_QECertChecked region pB pC
end QEC.Bounds.BPTCommutingProjectorModel

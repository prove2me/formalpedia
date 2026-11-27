-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_basisMatrix_sq_9d2569546e77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:29.285021+00:00
-- url     : https://prove2.me/submissions/204b97ba-2e30-418d-b05d-f92cd482b659

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module
open scoped Kronecker
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open Classical
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : (basisMatrix K).det ^ 2 = ((discr K : ℤ) : ℂ) := by
  rw [basisMatrix_eq_embeddingsMatrixReindex,
    ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K ℂ),
    ← (equivReindex K).symm_symm, Algebra.discr_reindex ℚ (integralBasis K) (equivReindex K).symm,
    ← coe_discr]
  simp
end GroundTheory.Heights₂.Heights

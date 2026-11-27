-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RealSpace_norm_sq_eq_f71c520492db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:44.666987+00:00
-- url     : https://prove2.me/submissions/11ebcc8b-0cef-4541-8e80-78a54b776e75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RealSpace_inner_def_21a13e1f2e4d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K]
variable [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
variable (h : HermitianMetric K E)
open GroundTheory.Heights₂.Heights.RealSpace
namespace GroundTheory.Heights₂.Heights.RealSpace
theorem _root_.solution (x : RealSpace h) :
    ‖x‖ ^ 2 = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h x))).re := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
end GroundTheory.Heights₂.Heights.RealSpace

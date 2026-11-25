-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RealSpace_inner_def_21a13e1f2e4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:55.848463+00:00
-- url     : https://prove2.me/submissions/5b9c32b5-5b53-4d91-9c44-003bb4796a0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean

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
theorem _root_.solution (x y : RealSpace h) :
    inner ℝ x y = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h y))).re := rfl
end GroundTheory.Heights₂.Heights.RealSpace

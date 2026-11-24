-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:23.056522+00:00
-- url     : https://prove2.me/submissions/dc5a1d92-d703-46d9-87d8-7f73951ba136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor

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
open GroundTheory.Heights₂.Heights.FibreSpace
variable (h : HermitianMetric K E) (σ : K →+* ℂ)
namespace GroundTheory.Heights₂.Heights.FibreSpace
theorem _root_.solution (x y : Fibre σ E) :
    inner ℂ (equiv h σ x) (equiv h σ y) = (h.form σ).inner x y := rfl
end GroundTheory.Heights₂.Heights.FibreSpace

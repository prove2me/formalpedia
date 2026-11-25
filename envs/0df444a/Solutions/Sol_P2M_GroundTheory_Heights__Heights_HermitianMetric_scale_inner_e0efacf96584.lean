-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianMetric_scale_inner_e0efacf96584
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:18.80174+00:00
-- url     : https://prove2.me/submissions/f2245a77-c8bc-47b2-81b2-be69bc1d3e36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights
namespace HermitianMetric
theorem _root_.solution (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c)
    (σ : K →+* ℂ) (x y : Fibre σ E) :
    ((h.scale c hc).form σ).inner x y = ((c ^ 2 : ℝ) : ℂ) * (h.form σ).inner x y := rfl
end HermitianMetric
end GroundTheory.Heights₂.Heights

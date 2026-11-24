-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:08.664499+00:00
-- url     : https://prove2.me/submissions/becbea72-81bb-4486-bf1a-8e56f7d1a0d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']
omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E']
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (z : ComplexAt σ) (e : E') :
    fibreMap σ f (z ⊗ₜ e) = z ⊗ₜ f e := rfl
end GroundTheory.Heights₂.Heights

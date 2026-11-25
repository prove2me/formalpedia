-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_baseChangeCoord_one_tmul_01fd286ad6c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:08.916456+00:00
-- url     : https://prove2.me/submissions/48f6fc74-ac00-4ad0-9bbc-8e0be4f54fca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (τ : L →+* ℂ) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] e)) =
      (1 : ComplexAt (τ.comp (algebraMap K L))) ⊗ₜ e := by
  rw [baseChangeCoord_tmul]
  congr 1
  simp
end GroundTheory.Heights₂.Heights.LatticeLemmas

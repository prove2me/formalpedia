-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_extend_mul_a7058f439749
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:36.327935+00:00
-- url     : https://prove2.me/submissions/688468a8-050d-4891-bbc9-70c091518bc0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

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
open NumberField Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι ι' : Type} [Fintype ι] [Fintype ι'] {j : ι → ι'}
    (hj : Function.Injective j) (a : ι → ℤ) (r : ι' → ℝ) :
    ∑ k', ((Function.extend j a 0 k' : ℤ) : ℝ) * r k' = ∑ k, (a k : ℝ) * r (j k) := by
  classical
  symm
  refine Fintype.sum_of_injective j hj _ _ (fun k' hk' ↦ ?_) (fun k ↦ ?_)
  · rw [Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ ↦ hk' ⟨k, hk⟩), Pi.zero_apply, Int.cast_zero,
      zero_mul]
  · rw [hj.extend_apply]
end GroundTheory.Heights₂.Heights

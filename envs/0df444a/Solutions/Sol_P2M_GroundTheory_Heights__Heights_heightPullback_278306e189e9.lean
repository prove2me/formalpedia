-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightPullback_278306e189e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:51.403404+00:00
-- url     : https://prove2.me/submissions/538d2626-5ec4-49c1-a3f1-a944461fc115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_heightLocalAgreement_7396ad881940
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_extend_mul_a7058f439749

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
theorem _root_.solution : HeightPullback.Statement := by
  intro ι ι' _ _ _ _ n' j hj A x hx
  have hxL : ∀ k i, x k i ∈ coordField x := fun k i ↦
    IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, rfl⟩
  have hpL : ∀ k i, HermLine.project j x k i ∈ coordField x := fun k i ↦ hxL (j k) i
  refine heightLocalAgreement ι' ι n' (n' ∘ j) (A.pullback j hj) A x (HermLine.project j x) hx
    (fun k ↦ hx (j k)) (coordField x) hxL hpL (fun v ↦ ?_) (fun σ ↦ rfl)
  unfold finiteTerm
  exact sum_extend_mul hj A.deg (fun k' ↦ Real.log (⨆ i, v (coordIn (coordField x) x hxL k' i)))
end GroundTheory.Heights₂.Heights

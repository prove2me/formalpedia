-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ordMod_eq_length_quot_sup_1026a45f8ec3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:58.417816+00:00
-- url     : https://prove2.me/submissions/0dbb0ef7-e62c-4498-bd50-12bd86c8c7ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (p : PrimeSpectrum A) (x : A) :
    ordMod p x = length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x})) := by
  rw [← length_coker_quot p x]
  have hr : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) x) =
      Submodule.map (p.asIdeal : Submodule A A).mkQ (Ideal.span {x} : Submodule A A) := by
    ext y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ z
      exact ⟨c * x, ⟨c, rfl⟩, by rw [← hz, Submodule.mkQ_apply, Submodule.mkQ_apply,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]⟩
    · rintro ⟨a, ⟨c, rfl⟩, hab⟩
      exact ⟨Submodule.mkQ _ c, by rw [← hab, Submodule.mkQ_apply, Submodule.mkQ_apply,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]⟩
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)).length_eq
end GroundTheory.Heights₂.Heights.NumbersDVR

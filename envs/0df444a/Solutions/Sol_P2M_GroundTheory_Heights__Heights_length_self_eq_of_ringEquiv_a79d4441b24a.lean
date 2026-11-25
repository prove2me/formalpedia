-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_self_eq_of_ringEquiv_a79d4441b24a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:23.241736+00:00
-- url     : https://prove2.me/submissions/015268f6-4864-4ed3-aed4-ff2e977baadd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalizeQuotientStages

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
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C) :
    Module.length A A = Module.length C C := by
  have : RingHomSurjective (e : A →+* C) := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* C)] C :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]
end GroundTheory.Heights₂.Heights

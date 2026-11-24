-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_linearEquiv_fa7014fc8534
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:05.363212+00:00
-- url     : https://prove2.me/submissions/58eb2e54-9e78-4458-9333-aaadb1a8d826

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7

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
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]
namespace GroundTheory.Heights₂.Heights.GenericFreeness
namespace IsGenericallyFree
theorem _root_.solution {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (e : M ≃ₗ[A] M') (hM : IsGenericallyFree A M) : IsGenericallyFree A M' := by
  obtain ⟨f, hf, hfree⟩ := hM
  refine ⟨f, hf, ?_⟩
  exact (free_iff_of_isLocalizedModule f
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M ∘ₗ e.symm.toLinearMap) (Localization.Away f)).1 hfree
end IsGenericallyFree
end GroundTheory.Heights₂.Heights.GenericFreeness

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_smul_eq_zero_16718e8e445b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:36.887619+00:00
-- url     : https://prove2.me/submissions/db439b2b-c6a3-4785-84f4-f22139bb3fb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module A M] (a : A) (ha : a ≠ 0)
    (h : ∀ m : M, a • m = 0) : IsGenericallyFree A M := by
  refine ⟨a, ha, ?_⟩
  have h0 : ∀ x : LocalizedModule (Submonoid.powers a) M, x = 0 := fun x ↦ by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      exact LocalizedModule.eq_zero_of_smul_eq_zero a (Submonoid.mem_powers a) _
        (by rw [LocalizedModule.smul'_mk, h, LocalizedModule.zero_mk])
  haveI : Subsingleton (LocalizedModule (Submonoid.powers a) M) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  infer_instance
end GroundTheory.Heights₂.Heights.GenericFreeness

-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.emb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:07.97914+00:00
-- url     : https://prove2.me/submissions/19feb46e-f04b-4ed0-bd35-075c61a0cd1d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution (hA : Function.Injective (algebraMap F A)) {κ : Type} : Function.Injective (emb (F := F) A κ) := by
  intro a b hab
  rw [emb_apply, emb_apply] at hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))
end PositivityTheory.ThKF0.Geo

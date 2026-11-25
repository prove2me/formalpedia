-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.emb_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:03.166442+00:00
-- url     : https://prove2.me/submissions/ea6b4791-5607-4072-a32e-3b5b70a5f853

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_om_apply
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
theorem _root_.solution {κ : Type} [Fintype κ] (a b : (κ → F) × (κ → F)) :
    (emb A κ a).1 ⬝ᵥ (emb A κ b).2 - (emb A κ b).1 ⬝ᵥ (emb A κ a).2 = algebraMap F A (om F κ a b) := by
  simp [emb_apply, om_apply, dotProduct]
end PositivityTheory.ThKF0.Geo

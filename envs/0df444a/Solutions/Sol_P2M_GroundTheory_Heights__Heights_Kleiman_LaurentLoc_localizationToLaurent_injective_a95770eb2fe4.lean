-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_injective_a95770eb2fe4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:04.411315+00:00
-- url     : https://prove2.me/submissions/09301b9c-310f-444a-a0a2-23d5c06d1fde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (I : Finset (Fin (N + 1))) : Function.Injective (iotaP (S := S) (N := N) I) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using LocalizedModule.induction_on with
  | h p s =>
    rw [localizationToLaurent_mk_eq_iff, mul_zero, ← map_zero (toL S N)] at hz
    rw [toL_injective S N hz]
    exact LocalizedModule.zero_mk s
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_res_6adc7ab2d94b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:10.448478+00:00
-- url     : https://prove2.me/submissions/f1f22862-9a6c-4c7c-9d1f-33220d32d9bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_mul_iotaP_a8c240395230
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_apply_bc280d50aeac

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
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (I J : StdCell N) (h : I.1 ⊆ J.1) (z : LocMod S N (Poly S N) I.1) :
    iota J (locResS I J h z) = iota I z := by
  rw [iota_apply, iota_apply]
  congr 1
  induction z using LocalizedModule.induction_on with
  | h p s =>
    change iotaP J.1 (locRes h (LocalizedModule.mk p s)) = _
    rw [locRes_mk, localizationToLaurent_mk_eq_iff]
    exact toL_mul_iotaP I.1 p s
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc

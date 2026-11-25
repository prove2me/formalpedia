-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_mk_e45328b2e1ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:41.727223+00:00
-- url     : https://prove2.me/submissions/4991225a-3ae9-4694-a395-331afcdf313d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8
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
theorem _root_.solution (I : StdCell N) (p : Poly S N) :
    iota I (locMk (Poly S N) I.1 p) = polyToLaurent S N p := by
  rw [iota_apply, ← coeff_toL]
  congr 1
  change iotaP I.1 (LocalizedModule.mk p 1) = _
  rw [localizationToLaurent_mk_eq_iff]
  change _ = toL S N 1 * _
  rw [map_one, one_mul]
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc

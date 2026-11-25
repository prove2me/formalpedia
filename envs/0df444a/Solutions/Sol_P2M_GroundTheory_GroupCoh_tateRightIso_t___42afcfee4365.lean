-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateRightIso_t___42afcfee4365
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:40.845809+00:00
-- url     : https://prove2.me/submissions/6fdd65a5-55f0-4a28-b380-593a92743ae4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorLeft_shortExact
import Theorems.Thm_P2M_GroundTheory_GroupCoh_t__comp_t__09d0113656ad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
variable {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact)
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) (hAE : (E.map (tensorLeft A)).ShortExact) (r : ℤ)
    (z : tateCohomology (A ⊗ E.X₃) r) :
    (tateRightIso A E.X₁ (r + 1)).hom.hom ((tδ hAE r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensorLeft hE A (augIdeal k G) hAE) (r + 1) (r + 1 + 1)
        rfl).hom ((tateRightIso A E.X₃ r).hom.hom z) := by
  have key := tδ_comp_tδ ((E.map (augSES k G)).map ((tensorLeft A).mapShortComplex))
    (augSES_tensorLeft_shortExact A E.X₁) (augSES_tensorLeft_shortExact A E.X₂)
    (augSES_tensorLeft_shortExact A E.X₃)
    (shortExact_tensorLeft_tensorLeft hE A (augIdeal k G) hAE)
    (shortExact_tensorLeft_tensorLeft hE A (Rep.leftRegular k G) hAE) hAE r
  have e := congr(($key).hom z)
  exact e
end GroundTheory.GroupCoh

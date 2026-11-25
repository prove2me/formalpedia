-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateLeftIso_t___8e34a8e92af3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:32.939656+00:00
-- url     : https://prove2.me/submissions/deef2fd1-7c58-46d9-80c5-6386df9a2205

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorRight_shortExact
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
    (tateLeftIso A E.X₁ (r + 1)).hom.hom ((tδ hAE r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensor hE A (augIdeal k G) hAE) (r + 1) (r + 1 + 1) rfl).hom
        ((tateLeftIso A E.X₃ r).hom.hom z) := by
  have key := tδ_comp_tδ (tensorShortComplex ((augSES k G).obj A) E)
    (shortExact_tensorLeft_tensor hE A (augIdeal k G) hAE)
    (shortExact_tensorLeft_tensor hE A (Rep.leftRegular k G) hAE) hAE
    (augSES_tensorRight_shortExact A E.X₁) (augSES_tensorRight_shortExact A E.X₂)
    (augSES_tensorRight_shortExact A E.X₃) r
  have e := congr(($key).hom z)
  exact (neg_eq_iff_eq_neg.mpr e).symm
end GroundTheory.GroupCoh

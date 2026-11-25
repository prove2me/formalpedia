-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_augShift__t__a3711d47d084
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:19.342558+00:00
-- url     : https://prove2.me/submissions/82b7f06f-c3ea-46f8-acb3-05c69a3ad575

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Theorems.Thm_GroundTheory_GroupCoh_augSES_shortExact
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
theorem _root_.solution (p : ℤ) (a : tateCohomology E.X₃ p) :
    (augShiftδ E.X₁ (p + 1)).hom ((tδ hE p (p + 1) rfl).hom a) =
      -(tδ (shortExact_tensorLeft_of_flat hE (augIdeal k G)) (p + 1) (p + 1 + 1) rfl).hom
        ((augShiftδ E.X₃ p).hom a) := by
  have key := tδ_comp_tδ (E.map (augSES k G))
    (augSES_shortExact E.X₁) (augSES_shortExact E.X₂) (augSES_shortExact E.X₃)
    (shortExact_tensorLeft_of_flat hE (augIdeal k G))
    (shortExact_tensorLeft_of_flat hE (Rep.leftRegular k G)) hE p
  have e := congr(($key).hom a)
  exact e
end GroundTheory.GroupCoh

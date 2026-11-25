-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateLeftIso_t__34419956ee59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:46.49094+00:00
-- url     : https://prove2.me/submissions/c883052d-bf27-4662-9e86-78bda23a9a5d

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
theorem _root_.solution (B : Rep.{u} k G) (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ)
    (z : tateCohomology (E.X₃ ⊗ B) r) :
    (tateLeftIso E.X₁ B (r + 1)).hom.hom ((tδ hEB r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensorRight hE B (augIdeal k G) hEB) (r + 1) (r + 1 + 1)
        rfl).hom ((tateLeftIso E.X₃ B r).hom.hom z) := by
  have key := tδ_comp_tδ ((E.map (augSES k G)).map ((tensorRight B).mapShortComplex))
    (augSES_tensorRight_shortExact E.X₁ B) (augSES_tensorRight_shortExact E.X₂ B)
    (augSES_tensorRight_shortExact E.X₃ B)
    (shortExact_tensorLeft_tensorRight hE B (augIdeal k G) hEB)
    (shortExact_tensorLeft_tensorRight hE B (Rep.leftRegular k G) hEB) hEB r
  have e := congr(($key).hom z)
  exact e
end GroundTheory.GroupCoh

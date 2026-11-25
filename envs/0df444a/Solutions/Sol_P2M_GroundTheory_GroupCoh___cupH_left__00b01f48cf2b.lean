-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___cupH_left__00b01f48cf2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:32.442417+00:00
-- url     : https://prove2.me/submissions/cf4ca118-a179-46c7-a4c5-0ec0055282f7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_P2M_GroundTheory_GroupCoh___cupH_left_a76c05aac289

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
variable (B : Rep k G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (hXB : (X.map (tensorRight B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : p + q = n) (h' : p' + q = m)
    (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n m hm (cupH h a b) = cupH h' (δ hX p p' hp a) b := by
  subst hp hm
  exact δ_cupH_left hX B hXB h h' a b
end GroundTheory.GroupCoh

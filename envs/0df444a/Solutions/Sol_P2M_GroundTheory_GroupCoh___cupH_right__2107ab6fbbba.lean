-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___cupH_right__2107ab6fbbba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:24:55.053571+00:00
-- url     : https://prove2.me/submissions/ff38e149-d211-43b9-8405-35157e149434

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_P2M_GroundTheory_GroupCoh___cupH_right_90f73d584671

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
theorem _root_.solution (hBX : (X.map (tensorLeft B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : q + p = n) (h' : q + p' = m)
    (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n m hm (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p p' hp a) := by
  subst hp hm
  exact δ_cupH_right hX B hBX h h' b a
end GroundTheory.GroupCoh

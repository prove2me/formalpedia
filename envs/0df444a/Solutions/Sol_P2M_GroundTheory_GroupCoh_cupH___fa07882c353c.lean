-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:57.692512+00:00
-- url     : https://prove2.me/submissions/b8e666da-1aca-4739-a214-1299501c0f6e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_TateCohomology_CupProduct

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
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    cupH h (π A p z) (π B q w) = π (A ⊗ B) n (cupCocycles h z w) := by
  rw [cupH, descH_π]
  exact cupHLeft_π h z w
end GroundTheory.GroupCoh

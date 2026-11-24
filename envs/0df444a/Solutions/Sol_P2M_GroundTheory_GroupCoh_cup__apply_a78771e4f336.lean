-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:39.914857+00:00
-- url     : https://prove2.me/submissions/8b6affc5-e613-4ce5-9a83-f4a3024591b4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains

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
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    cupₗ h f g = cupCochain h f g :=
  rfl
end GroundTheory.GroupCoh

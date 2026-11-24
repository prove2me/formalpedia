-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:42.697895+00:00
-- url     : https://prove2.me/submissions/badbc7f8-7689-4334-9fd9-1c09e1a090b0

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
theorem _root_.solution (X Y : Rep k G) (s : G) (a : X) (b : Y) :
    (X ⊗ Y).ρ s (a ⊗ₜ[k] b) = X.ρ s a ⊗ₜ[k] Y.ρ s b :=
  rfl
end GroundTheory.GroupCoh

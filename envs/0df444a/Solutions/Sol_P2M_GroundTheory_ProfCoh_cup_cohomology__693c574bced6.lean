-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cup_cohomology__693c574bced6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:39.558236+00:00
-- url     : https://prove2.me/submissions/16160504-955f-414c-9460-e3e1b2541a88

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_Bridge
import Definitions.Def_GroundTheory_ProfiniteCohomology_CupProducts

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
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G]
variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}
namespace GroundTheory.ProfCoh
theorem _root_.solution (h : p + q = n) (x : GroundTheory.ProfCoh.cocycles A p) (y : GroundTheory.ProfCoh.cocycles B q) :
    cup h (cohomologyπ A p x) (cohomologyπ B q y) = cohomologyπ (A ⊗ B) n (cupCocycles h x y) := by
  rw [cup, descCohomology_cohomologyπ, LinearMap.flip_apply, cup_cohomology_class]
  rfl
end GroundTheory.ProfCoh

-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_d___apply_eq_sum_78c801493460
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:51.926343+00:00
-- url     : https://prove2.me/submissions/1dae424e-1728-4f72-b0d4-936bfe5b82b3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (z : G →₀ A) :
    d₁₀ A z = ∑ g ∈ z.support, (A.ρ g⁻¹ (z g) - z g) := by
  change (Finsupp.lsum k fun g => A.ρ g⁻¹ - LinearMap.id) z = _
  rw [Finsupp.lsum_apply, Finsupp.sum]
  rfl
end GroundTheory.GroupCoh

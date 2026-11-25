-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:36:22.683554+00:00
-- url     : https://prove2.me/submissions/4ce60e58-0baf-4909-af52-79ac39a9383c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_tateIsoH_homology_class_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep k G) (n : ℕ) [NeZero n] (z : (tateComplex A).cycles n) :
    (tateIsoH A n n rfl).hom.hom (((tateComplex A).homologyπ n).hom z) =
      π A n (cocyclesMk (((tateComplex A).iCycles n).hom z) (tate_d_iCycles A n z)) := by
  obtain ⟨C, h1, h2⟩ := tateIsoH_homology_class_eq A n
  have e1 : (tateIsoH A n n rfl).hom.hom (((tateComplex A).homologyπ n).hom z) =
      (π A n).hom (C.hom z) := congr(($h1).hom z)
  rw [e1]
  congr 1
  apply cocycles_ext
  refine (congr(($h2).hom z)).trans ?_
  exact (iCocycles_mk _ _).symm
end GroundTheory.GroupCoh

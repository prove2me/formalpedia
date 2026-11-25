-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_d___mapRange_f2a791e02ad3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:56.343658+00:00
-- url     : https://prove2.me/submissions/097368f2-f14a-45bd-a70a-c3b72f06bf44

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
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (f : A ⟶ B)
namespace GroundTheory.GroupCoh
theorem _root_.solution (y : G →₀ A) :
    d₁₀ B (Finsupp.mapRange.linearMap f.hom.toLinearMap y) = f.hom (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₁₀_single, d₁₀_single,
      map_sub, Rep.hom_comm_apply]
    rfl
end GroundTheory.GroupCoh

-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_d___mapRange_cf7c0094db79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:53.726796+00:00
-- url     : https://prove2.me/submissions/3b5e215a-022d-4d98-bd43-6465f447cc78

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
theorem _root_.solution (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange.linearMap f.hom.toLinearMap c) =
      Finsupp.mapRange.linearMap f.hom.toLinearMap (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₂₁_single, d₂₁_single,
      map_add, map_sub, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single,
      show f.hom.toLinearMap (A.ρ g.1⁻¹ a) = B.ρ g.1⁻¹ (f.hom.toLinearMap a) from
        Rep.hom_comm_apply f g.1⁻¹ a]
end GroundTheory.GroupCoh

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isOpen_saturate_bdd42cb5cc08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:26.901751+00:00
-- url     : https://prove2.me/submissions/fe1ad4c0-6706-426f-8f21-62b4f3a26744

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (Γ : Subgroup G) {A : Set G} (hA : IsOpen A) : IsOpen (saturate Γ A) := by
  have : saturate Γ A = ⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' A := by
    ext y; simp [saturate]
  rw [this]
  exact isOpen_iUnion fun γ => hA.preimage (by fun_prop)
end GroundTheory.Heights₂.Theta

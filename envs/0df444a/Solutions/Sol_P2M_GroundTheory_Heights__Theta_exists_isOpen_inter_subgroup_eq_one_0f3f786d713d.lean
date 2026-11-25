-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_isOpen_inter_subgroup_eq_one_0f3f786d713d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:50.450215+00:00
-- url     : https://prove2.me/submissions/340a3425-566b-4386-a9d1-e5da46af588a

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
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ γ ∈ Γ, γ ∈ W → γ = 1 := by
  have h1 : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp h1
  refine ⟨W, hW, ?_, ?_⟩
  · have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hWeq]; rfl
    simpa using this
  · intro γ hγ hγW
    have : (⟨γ, hγ⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := hγW
    rw [hWeq] at this
    simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp this)
end GroundTheory.Heights₂.Theta

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_isOpen_small_b5c2f2fc479e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:24.608302+00:00
-- url     : https://prove2.me/submissions/28ca7b0e-7cdb-4225-a584-c92d9c2e5e1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isOpen_inter_subgroup_eq_one_0f3f786d713d

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
theorem _root_.solution (Γ : Subgroup G) [DiscreteTopology Γ] (c : G) :
    ∃ V : Set G, IsOpen V ∧ c ∈ V ∧ (∃ L, IsCompact L ∧ V ⊆ L) ∧
      ∀ γ ∈ Γ, ∀ x ∈ V, γ * x ∈ V → γ = 1 := by
  obtain ⟨W, hWo, hW1, hWΓ⟩ := exists_isOpen_inter_subgroup_eq_one Γ
  have hcont : Continuous fun p : G × G => p.1 * p.2⁻¹ := by fun_prop
  have hmem : (c, c) ∈ (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' W := by simpa using hW1
  obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hsub⟩ :=
    isOpen_prod_iff.mp (hWo.preimage hcont) c c hmem
  obtain ⟨L, hL, hLn⟩ := exists_compact_mem_nhds c
  refine ⟨U₁ ∩ U₂ ∩ interior L, (hU₁.inter hU₂).inter isOpen_interior,
    ⟨⟨hc₁, hc₂⟩, mem_interior_iff_mem_nhds.mpr hLn⟩, ⟨L, hL, fun x hx => interior_subset hx.2⟩, ?_⟩
  intro γ hγ x hx hγx
  apply hWΓ γ hγ
  have : (γ * x, x) ∈ U₁ ×ˢ U₂ := ⟨hγx.1.1, hx.1.2⟩
  simpa using hsub this
end GroundTheory.Heights₂.Theta

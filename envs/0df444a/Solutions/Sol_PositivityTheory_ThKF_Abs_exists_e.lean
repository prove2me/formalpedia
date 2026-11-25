-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.exists_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:23.037089+00:00
-- url     : https://prove2.me/submissions/e138b7cb-0551-405b-a018-c98e0da32a1c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Theorems.Thm_PositivityTheory_ThKF_Abs_proj_equiv
import Theorems.Thm_PositivityTheory_ThKF_Abs_span_orbit_stab
import Theorems.Thm_PositivityTheory_ThKF_Abs_mem_orb
import Theorems.Thm_PositivityTheory_ThKF_Abs_fd_orth
import Theorems.Thm_PositivityTheory_ThKF_Abs_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace PositivityTheory.ThKF.Abs
theorem _root_.solution {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) (f : U) (hH : FiniteDimensional ℂ (homs κ (orb κ f))) :
    ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
      ∀ S : Submodule ℂ U, (∀ k, ∀ y ∈ S, κ k y ∈ S) → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z := by
  have := hf f
  refine ⟨_, ck (homs κ (orb κ f)), fd_orth κ _, fun z hz => ?_, rfl, fun S hS u hu => ?_⟩
  · have h0 : (orb κ f).starProjection z = 0 := hz ((orb κ f).starProjection : U →ₗ[ℂ] U)
      ⟨fun x => (orb κ f).starProjection_apply_mem x, fun k x => proj_equiv κ hi (orb κ f) (span_orbit_stab κ f) k x⟩
    have h1 := (orb κ f).sub_starProjection_mem_orthogonal z
    rw [h0, sub_zero] at h1
    rw [inner_eq_zero_symm]
    exact h1 f (mem_orb κ f)
  · have := hf u
    have VS : orb κ u ≤ S := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k u hu)
    obtain ⟨y, hy, z, hz, h⟩ := split κ hi (orb κ f) (orb κ u) (span_orbit_stab κ u) u (mem_orb κ u)
    exact ⟨y, VS hy, z, VS hz, h⟩
end PositivityTheory.ThKF.Abs

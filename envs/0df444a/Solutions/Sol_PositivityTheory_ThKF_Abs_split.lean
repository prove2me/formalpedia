-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:48.865797+00:00
-- url     : https://prove2.me/submissions/097ae435-ea6c-48a2-83ee-389890e4d69e

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Theorems.Thm_PositivityTheory_ThKF_Abs_orth_stab
import Theorems.Thm_PositivityTheory_ThKF_Abs_proj_equiv

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
    (W V : Submodule ℂ U) [FiniteDimensional ℂ V] (sV : ∀ k, ∀ y ∈ V, κ k y ∈ V) (u : U) (uV : u ∈ V) :
    ∃ y ∈ V, ∃ z ∈ V, y ∈ (ck (homs κ W))ᗮ ∧ z ∈ ck (homs κ W) ∧ u = y + z := by
  have sZ' : ∀ k, ∀ z ∈ ck (homs κ W), κ k z ∈ ck (homs κ W) := fun k z hz L hL => by rw [hL.2, hz L hL, map_zero]
  obtain ⟨A, hA⟩ : ∃ A, A = V ⊓ ck (homs κ W) := ⟨_, rfl⟩
  have : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := V) (hA ▸ inf_le_left)
  have mA : ∀ y, y ∈ A ↔ y ∈ V ∧ y ∈ ck (homs κ W) := fun y => by rw [hA]; rfl
  have sA : ∀ k, ∀ y ∈ A, κ k y ∈ A := fun k y hy => (mA _).2 ⟨sV k y ((mA _).1 hy).1, sZ' k y ((mA _).1 hy).2⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = V ⊓ Aᗮ := ⟨_, rfl⟩
  have : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le (S₂ := V) (hY ▸ inf_le_left)
  have mY : ∀ y, y ∈ Y ↔ y ∈ V ∧ y ∈ Aᗮ := fun y => by rw [hY]; rfl
  have sY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y := fun k y hy =>
    (mY _).2 ⟨sV k y ((mY _).1 hy).1, orth_stab κ hi A sA k y ((mY _).1 hy).2⟩
  have hz := (mA _).1 (A.starProjection_apply_mem u)
  have hy : u - A.starProjection u ∈ Y := (mY _).2 ⟨sub_mem uV hz.1, A.sub_starProjection_mem_orthogonal u⟩
  refine ⟨_, ((mY _).1 hy).1, _, hz.1, fun z hz' => ?_, hz.2, (sub_add_cancel _ _).symm⟩
  have h1 : Y.starProjection z ∈ ck (homs κ W) := fun L hL =>
    hz' (L ∘ₗ (Y.starProjection : U →ₗ[ℂ] U)) ⟨fun x => hL.1 _, fun k x => by
      show L (Y.starProjection (κ k x)) = κ k (L (Y.starProjection x))
      rw [proj_equiv κ hi Y sY, hL.2]⟩
  have h2 := (mY _).1 (Y.starProjection_apply_mem z)
  have h3 : Y.starProjection z = 0 := inner_self_eq_zero.1 (h2.2 _ ((mA _).2 ⟨h2.1, h1⟩))
  have h4 := Y.sub_starProjection_mem_orthogonal z
  rw [h3, sub_zero] at h4
  rw [inner_eq_zero_symm]
  exact h4 _ hy
end PositivityTheory.ThKF.Abs

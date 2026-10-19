-- Prove2me | solution 1 for SoficGroups.inner_sq_le_of_finite_orthogonal_sector_splitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/d7b9c53b-1d22-4df5-b0f5-53a24d684e56

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_inner_sq_le_of_orthogonal_two_sector

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (F : ι → Submodule ℂ H)
    [∀ i, (F i).HasOrthogonalProjection]
    (U V : Submodule ℂ H)
    (hU : ∀ (i : ι) ⦃x : H⦄, x ∈ U →
      (F i).starProjection x ∈ U)
    (hV : ∀ (i : ι) ⦃x : H⦄, x ∈ V →
      (F i).starProjection x ∈ V)
    (hF : ∀ (i j : ι) ⦃x : H⦄, x ∈ F j →
      (F i).starProjection x ∈ F j)
    (hsector : ∀ (i : ι) (a b : H),
      a ∈ U → b ∈ V → a ∈ (F i)ᗮ → b ∈ (F i)ᗮ →
        8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2)
    (hterminal : ∀ (a b : H), a ∈ U → b ∈ V →
      (∀ i, a ∈ F i) → (∀ i, b ∈ F i) → inner ℂ a b = 0)
    (a b : H) (ha : a ∈ U) (hb : b ∈ V) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  classical
  have hind : ∀ (s : Finset ι) (x y : H),
      x ∈ U → y ∈ V →
      (∀ j, j ∉ s → x ∈ F j) →
      (∀ j, j ∉ s → y ∈ F j) →
      8 * ‖inner ℂ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro x y hx hy hxF hyF
        have hzero : inner ℂ x y = 0 :=
          hterminal x y hx hy
            (fun j => hxF j (by simp))
            (fun j => hyF j (by simp))
        simpa [hzero] using
          mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)
    | @insert i s hi ih =>
        intro x y hx hy hxF hyF
        let x₀ : H := (F i).starProjection x
        let x₁ : H := (F i)ᗮ.starProjection x
        let y₀ : H := (F i).starProjection y
        let y₁ : H := (F i)ᗮ.starProjection y
        have hx₀ : x₀ ∈ U := hU i hx
        have hy₀ : y₀ ∈ V := hV i hy
        have hx₁ : x₁ ∈ U := by
          dsimp [x₁]
          rw [Submodule.starProjection_orthogonal_val]
          exact U.sub_mem hx (hU i hx)
        have hy₁ : y₁ ∈ V := by
          dsimp [y₁]
          rw [Submodule.starProjection_orthogonal_val]
          exact V.sub_mem hy (hV i hy)
        have hx₀i : x₀ ∈ F i :=
          Submodule.starProjection_apply_mem (F i) x
        have hy₀i : y₀ ∈ F i :=
          Submodule.starProjection_apply_mem (F i) y
        have hx₁i : x₁ ∈ (F i)ᗮ :=
          Submodule.starProjection_apply_mem (F i)ᗮ x
        have hy₁i : y₁ ∈ (F i)ᗮ :=
          Submodule.starProjection_apply_mem (F i)ᗮ y
        have hx₀F : ∀ j, j ∉ s → x₀ ∈ F j := by
          intro j hj
          by_cases hji : j = i
          · subst j
            exact hx₀i
          · apply hF i j
            apply hxF j
            simp [hji, hj]
        have hy₀F : ∀ j, j ∉ s → y₀ ∈ F j := by
          intro j hj
          by_cases hji : j = i
          · subst j
            exact hy₀i
          · apply hF i j
            apply hyF j
            simp [hji, hj]
        have h₀ :
            8 * ‖inner ℂ x₀ y₀‖ ^ 2 ≤
              ‖x₀‖ ^ 2 * ‖y₀‖ ^ 2 :=
          ih x₀ y₀ hx₀ hy₀ hx₀F hy₀F
        have h₁ :
            8 * ‖inner ℂ x₁ y₁‖ ^ 2 ≤
              ‖x₁‖ ^ 2 * ‖y₁‖ ^ 2 :=
          hsector i x₁ y₁ hx₁ hy₁ hx₁i hy₁i
        have hsumx : x₀ + x₁ = x :=
          (F i).starProjection_add_starProjection_orthogonal x
        have hsumy : y₀ + y₁ = y :=
          (F i).starProjection_add_starProjection_orthogonal y
        have htwo := inner_sq_le_of_orthogonal_two_sector
          x₀ x₁ y₀ y₁
          (Submodule.inner_right_of_mem_orthogonal hx₀i hx₁i)
          (Submodule.inner_right_of_mem_orthogonal hy₀i hy₁i)
          (Submodule.inner_right_of_mem_orthogonal hx₀i hy₁i)
          (Submodule.inner_left_of_mem_orthogonal hy₀i hx₁i)
          h₀ h₁
        rwa [hsumx, hsumy] at htwo
  apply hind Finset.univ a b ha hb
  · intro j hj
    exact (hj (Finset.mem_univ j)).elim
  · intro j hj
    exact (hj (Finset.mem_univ j)).elim
end SoficGroups

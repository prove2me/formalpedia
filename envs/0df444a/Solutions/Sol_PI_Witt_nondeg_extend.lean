-- Prove2me | solution 1 for PI.Witt.nondeg_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:21:18.230086+00:00
-- url     : https://prove2.me/submissions/24b4eaac-7335-40a3-ad08-7786a544258b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Nondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
namespace PI.Witt
theorem _root_.solution (h1 : OneVector) (h2 : Anisotropic) [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) :
    ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U = n →
      (∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0) →
      ∀ f : U →ₗ[K] V, (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ (∀ x : U, g x = f x) ∧
        ∀ z, (∀ u : U, B (u : V) z = 0) → (∀ u : U, B (f u) z = 0) → g z = z := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro U hU hnd f hf
  by_cases hex : ∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0
  · obtain ⟨u, hu, hBu⟩ := h2 K V B hB U hex
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ :=
      h1 K V B hB u (f ⟨u, hu⟩) (hf ⟨u, hu⟩ ⟨u, hu⟩).symm hBu
    have hsym : ∀ a b, B (g₁.symm a) b = B a (g₁ b) := by
      intro a b
      rw [← hg₁ (g₁.symm a) b, LinearEquiv.apply_symm_apply]
    have hsym₂ : ∀ a b, B (g₁.symm a) (g₁.symm b) = B a b := by
      intro a b
      rw [hsym, LinearEquiv.apply_symm_apply]
    let U' : Submodule K V := U ⊓ LinearMap.ker (B u)
    have hle : U' ≤ U := inf_le_left
    have hker : ∀ w ∈ U', B u w = 0 := fun w hw => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2
    have hwu : ∀ w ∈ U', B w u = 0 := by
      intro w hw
      rw [← hB u w, hker w hw, star_zero]
    have hproj : ∀ y ∈ U, y - (B u y / B u u) • u ∈ U' := by
      intro y hy
      refine Submodule.mem_inf.mpr ⟨U.sub_mem hy (U.smul_mem _ hu), LinearMap.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hBu, sub_self]
    have hlt : Module.finrank K U' < n := by
      rw [← hU]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle fun heq => hBu ?_)
      have hu' : u ∈ U' := by rw [heq]; exact hu
      exact hker u hu'
    have hnd' : ∀ x ∈ U', (∀ y ∈ U', B x y = 0) → x = 0 := by
      intro x hx hxy
      refine hnd x (hle hx) fun y hy => ?_
      have h := hxy _ (hproj y hy)
      rw [map_sub, map_smul, hwu x hx, smul_zero, sub_zero] at h
      exact h
    let f' : U' →ₗ[K] V := g₁.symm.toLinearMap ∘ₗ f ∘ₗ Submodule.inclusion hle
    have hf'x : ∀ x : U', f' x = g₁.symm (f (Submodule.inclusion hle x)) := fun x => rfl
    have hf' : ∀ x y : U', B (f' x) (f' y) = B x y := by
      intro x y
      rw [hf'x, hf'x, hsym₂, hf]
      rfl
    obtain ⟨g₂, hg₂, hg₂f, hg₂fix⟩ := ih _ hlt U' rfl hnd' f' hf'
    have hg₂u : g₂ u = u := by
      refine hg₂fix u (fun w => hwu w w.2) fun w => ?_
      rw [hf'x, hsym, hg₁u, hf]
      exact hwu w w.2
    refine ⟨g₂.trans g₁, fun x y => ?_, fun x => ?_, fun z hz₁ hz₂ => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      rw [hg₁, hg₂]
    · obtain ⟨c, hc⟩ : ∃ c : K, c = B u x / B u u := ⟨_, rfl⟩
      have hmem : (x : V) - c • u ∈ U' := hc ▸ hproj x x.2
      let x' : U' := ⟨_, hmem⟩
      have hxv : (x : V) = c • u + (x' : V) := by simp [x']
      have hxU : x = c • (⟨u, hu⟩ : U) + Submodule.inclusion hle x' := Subtype.ext (by simp [x'])
      calc (g₂.trans g₁) (x : V) = g₁ (g₂ (c • u + (x' : V))) := by rw [← hxv]; rfl
        _ = c • g₁ u + g₁ (f' x') := by
            rw [map_add, map_smul, hg₂u, hg₂f x', map_add, map_smul]
        _ = f x := by
            rw [hg₁u, hf'x, LinearEquiv.apply_symm_apply]
            conv_rhs => rw [hxU]
            rw [map_add, map_smul]
    · have hg₁z : g₁ z = z := hg₁fix z (hz₁ ⟨u, hu⟩) (hz₂ ⟨u, hu⟩)
      have hg₂z : g₂ z = z := by
        refine hg₂fix z (fun w => hz₁ (Submodule.inclusion hle w)) fun w => ?_
        rw [hf'x, hsym, hg₁z]
        exact hz₂ _
      show g₁ (g₂ z) = z
      rw [hg₂z, hg₁z]
  · push Not at hex
    refine ⟨LinearEquiv.refl K V, fun x y => rfl, fun x => ?_, fun z _ _ => rfl⟩
    have hx0 : x = 0 := Subtype.ext (hnd x x.2 (hex x x.2))
    subst hx0
    simp
end PI.Witt

-- Prove2me | solution 1 for RibetLevelLowering.gramSnake_ker_and_coker_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bb6a3b59-362b-5101-9612-640cec4d9df4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetLevelLowering_gramSnake_ker_and_coker_transfer

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R]
    {Y L X Yd Ld Xd : Type*}
    [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L] [AddCommGroup X] [Module R X]
    [AddCommGroup Yd] [Module R Yd] [AddCommGroup Ld] [Module R Ld] [AddCommGroup Xd] [Module R Xd]
    (ι : Y →ₗ[R] L) (δ : L →ₗ[R] X) (hδι : ∀ y : Y, δ (ι y) = 0)
    (σ : X →ₗ[R] L) (η : R) (hσ : ∀ x : X, δ (σ x) = η • x)
    (κd : Xd →ₗ[R] Ld) (ρd : Ld →ₗ[R] Yd) (hρd : Function.Surjective ρd)
    (hdc : ∀ φ : Xd, ρd (κd φ) = 0) (hexd : ∀ l : Ld, ρd l = 0 → ∃ φ : Xd, κd φ = l)
    (gL : L →ₗ[R] Ld) (hgL : Function.Injective gL) (gX : X →ₗ[R] Xd) (gY : Y →ₗ[R] Yd)
    (hsq : ∀ x : X, gL (σ x) = κd (gX x))
    (hres : ∀ y : Y, gY y = ρd (gL (ι y))) :
    let Θ : L →ₗ[R] (Yd ⧸ LinearMap.range gY) := (LinearMap.range gY).mkQ ∘ₗ ρd ∘ₗ gL
    (∀ y : Y, Θ (ι y) = 0) ∧
    (∀ x : X, Θ (σ x) = 0) ∧
    (∀ u : R, (∀ φ : Xd, ∃ x : X, u • φ = gX x) →
        ∀ l : L, Θ l = 0 → ∃ x₁ : X, u • δ l = η • x₁) ∧
    (∀ u : R, (∀ m : Ld, ∃ l : L, u • m = gL l) →
        ∀ ψ : Yd ⧸ LinearMap.range gY, ∃ l : L, u • ψ = Θ l) := by
  intro Θ
  have hΘ : ∀ l : L, Θ l = (LinearMap.range gY).mkQ (ρd (gL l)) := fun l => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro y
    rw [hΘ, ← hres, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self gY y
  ·
    intro x
    rw [hΘ, hsq, hdc, map_zero]
  ·
    intro u hu l hl
    rw [hΘ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hl
    obtain ⟨y, hy⟩ := hl
    rw [hres] at hy

    have h0 : ρd (gL (l - ι y)) = 0 := by rw [map_sub, map_sub, hy, sub_self]
    obtain ⟨φ, hφ⟩ := hexd _ h0
    obtain ⟨x₁, hx₁⟩ := hu φ
    have h1 : gL (u • (l - ι y)) = gL (σ x₁) := by
      rw [map_smul, ← hφ, ← map_smul, hx₁, ← hsq]
    have h2 : u • (l - ι y) = σ x₁ := hgL h1
    refine ⟨x₁, ?_⟩
    have h3 := congrArg δ h2
    rw [map_smul, map_sub, hδι, sub_zero, hσ] at h3
    exact h3
  ·
    intro u hu ψ
    obtain ⟨φ, rfl⟩ := (LinearMap.range gY).mkQ_surjective ψ
    obtain ⟨m, rfl⟩ := hρd φ
    obtain ⟨l, hl⟩ := hu m
    refine ⟨l, ?_⟩
    rw [hΘ, ← hl, map_smul, map_smul]

end S_RibetLevelLowering_gramSnake_ker_and_coker_transfer
end P2MW
export P2MW.S_RibetLevelLowering_gramSnake_ker_and_coker_transfer (solution)

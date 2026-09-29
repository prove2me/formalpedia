-- Prove2me | solution 1 for Representation.finrank_invariants_linHom_dual_twist_ofChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/426640a0-0589-532a-867f-a8d6fd85968c

import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_finrank_invariants_linHom_dual_twist_ofChar

set_option autoImplicit false
universe u
open Module
open scoped IntermediateField Pointwise

private theorem twist_trivial_apply_apply_T4a {k : Type*} [Field k] {Γ : Type*} [Group Γ]
    (ψ : Γ →* kˣ) (g : Γ) (x : k) : (Representation.trivial k Γ k).twist ψ g x = (ψ g : k) * x := rfl

theorem solution
    {k : Type*} [Field k] {Δ : Type*} [Group Δ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) (χ : Δ →* kˣ) :
    finrank k ((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)).invariants = finrank k ρ.invariants := by
  classical
  have hdt : ∀ (g : Δ) (f : Module.Dual k V), ρ.dual.twist χ g f = (χ g : k) • (f ∘ₗ ρ g⁻¹) := fun g f => by
    rw [Representation.twist_apply_apply, Representation.dual_apply, Module.Dual.transpose_apply]

  have hmem : ∀ φ : Module.Dual k V →ₗ[k] k,
      φ ∈ ((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)).invariants ↔
        ∀ (g : Δ) (f : Module.Dual k V), φ (f ∘ₗ ρ g) = φ f := by
    intro φ
    rw [Representation.mem_invariants]
    have hcalc : ∀ (g : Δ) (f : Module.Dual k V),
        (((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)) g φ) f =
          (χ g : k) * ((χ g⁻¹ : k) * φ (f ∘ₗ ρ g)) := by
      intro g f
      rw [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, hdt, inv_inv, map_smul,
        twist_trivial_apply_apply_T4a, smul_eq_mul]
    have hunit : ∀ g : Δ, (χ g : k) * (χ g⁻¹ : k) = 1 := fun g => by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine forall_congr' fun g => ?_
    constructor
    · intro h f
      have := LinearMap.congr_fun h f
      rw [hcalc, ← mul_assoc, hunit, one_mul] at this
      exact this
    · intro h
      apply LinearMap.ext
      intro f
      rw [hcalc, ← mul_assoc, hunit, one_mul]
      exact h f

  let ev := Module.evalEquiv k V
  have hev : ∀ (v : V) (f : Module.Dual k V), ev v f = f v := fun v f => rfl
  let e : ρ.invariants ≃ₗ[k] ((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)).invariants :=
    { toFun := fun v => ⟨ev (v : V), (hmem _).mpr fun g f => by
        rw [hev, hev, LinearMap.comp_apply]
        congr 1
        exact (Representation.mem_invariants ρ v).mp v.2 g⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
      invFun := fun φ => ⟨ev.symm (φ : Module.Dual k V →ₗ[k] k), (Representation.mem_invariants ρ _).mpr fun g => by
        apply ev.injective
        apply LinearMap.ext
        intro f
        rw [LinearEquiv.apply_symm_apply, hev, ← LinearMap.comp_apply f (ρ g), ← hev, LinearEquiv.apply_symm_apply]
        exact (hmem _).mp φ.2 g f⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun φ => Subtype.ext (by simp) }
  exact (LinearEquiv.finrank_eq e).symm

end S_Representation_finrank_invariants_linHom_dual_twist_ofChar
end P2MW
export P2MW.S_Representation_finrank_invariants_linHom_dual_twist_ofChar (solution)

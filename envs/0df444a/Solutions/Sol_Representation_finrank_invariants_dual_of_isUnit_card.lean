-- Prove2me | solution 1 for Representation.finrank_invariants_dual_of_isUnit_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2d49b1e0-9515-519d-bf19-dbfd543ca2b3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_finrank_invariants_dual_of_isUnit_card

set_option autoImplicit false
universe u
open Module
open scoped IntermediateField Pointwise

theorem solution
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) :
    finrank k ρ.dual.invariants = finrank k ρ.invariants := by
  classical
  haveI : Invertible ((Fintype.card Δ : k)) := hΔ.invertible

  have hmem : ∀ f : Module.Dual k V, f ∈ ρ.dual.invariants ↔ ∀ (g : Δ) (v : V), f (ρ g v) = f v := by
    intro f
    rw [Representation.mem_invariants]
    simp only [Representation.dual_apply, Module.Dual.transpose_apply]
    constructor
    · intro h g v
      have := LinearMap.congr_fun (h g⁻¹) v
      simpa using this
    · intro h g
      ext v
      exact h g⁻¹ v

  have hPρ : ∀ (g : Δ) (v : V), ρ.averageMap (ρ g v) = ρ.averageMap v := by
    intro g v
    have : ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
      rw [Representation.averageMap, ← Representation.asAlgebraHom_of, ← Module.End.mul_eq_comp, ← map_mul,
        MonoidAlgebra.of_apply, GroupAlgebra.mul_average_right]
    exact LinearMap.congr_fun this v

  have hfP : ∀ f : Module.Dual k V, (∀ (g : Δ) (v : V), f (ρ g v) = f v) → ∀ v, f (ρ.averageMap v) = f v := by
    intro f hf v
    have hexp : ρ.averageMap v = ⅟(Fintype.card Δ : k) • ∑ g : Δ, ρ g v := by
      simp [Representation.averageMap, GroupAlgebra.average, map_sum, LinearMap.sum_apply]
    rw [hexp, map_smul, map_sum]
    simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

  let Pc : V →ₗ[k] ρ.invariants := ρ.averageMap.codRestrict ρ.invariants ρ.averageMap_invariant
  have hPc : ∀ w : ρ.invariants, Pc w = w := fun w => Subtype.ext (ρ.averageMap_id w w.2)
  let e : ρ.dual.invariants ≃ₗ[k] Module.Dual k ρ.invariants :=
    { toFun := fun f => (f : Module.Dual k V) ∘ₗ ρ.invariants.subtype
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun φ => ⟨φ ∘ₗ Pc, (hmem _).mpr fun g v => by
        simp only [LinearMap.coe_comp, Function.comp_apply]
        congr 1
        exact Subtype.ext (hPρ g v)⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
        exact hfP f ((hmem _).mp f.2) v
      right_inv := fun φ => by
        apply LinearMap.ext
        intro w
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, hPc] }
  rw [LinearEquiv.finrank_eq e, Subspace.dual_finrank_eq]

end S_Representation_finrank_invariants_dual_of_isUnit_card
end P2MW
export P2MW.S_Representation_finrank_invariants_dual_of_isUnit_card (solution)

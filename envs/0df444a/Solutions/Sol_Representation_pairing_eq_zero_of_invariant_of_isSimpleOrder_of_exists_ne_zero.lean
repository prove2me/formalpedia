-- Prove2me | solution 1 for Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cb76f0d0-0fb1-58e0-9840-cc25b6986c40

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero

set_option autoImplicit false

theorem solution
    {k : Type*} [CommSemiring k] {K : Type*} [Group K]
    {S : Type*} [AddCommMonoid S] [Module k S] {S' : Type*} [AddCommMonoid S'] [Module k S']
    {X : Type*} [AddCommMonoid X] [Module k X]
    (ρ : Representation k K S) (ρ' : Representation k K S') [IsSimpleOrder (Subrepresentation ρ')]
    (β : S →ₗ[k] S' →ₗ[k] X) (hβ : ∀ (g : K) (s : S) (s' : S'), β (ρ g s) (ρ' g s') = β s s')
    (h0 : ∃ s' : S', s' ≠ 0 ∧ ∀ s : S, β s s' = 0) :
    β = 0 := by
  let N : Subrepresentation ρ' :=
    { toSubmodule :=
        { carrier := {s' | ∀ s : S, β s s' = 0}
          zero_mem' := fun s => by simp
          add_mem' := fun {a b} ha hb s => by simp [ha s, hb s]
          smul_mem' := fun c {a} ha s => by simp [ha s] }
      apply_mem_toSubmodule := fun g {s'} hs' s => by
        have := hβ g (ρ g⁻¹ s) s'
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        show β s (ρ' g s') = 0
        rw [this]; exact hs' _ }
  have hmem : ∀ s' : S', s' ∈ N ↔ ∀ s : S, β s s' = 0 := fun s' => Iff.rfl
  have hN : N ≠ ⊥ := by
    obtain ⟨s', hs'0, hs'⟩ := h0
    intro h
    have hs'N : s' ∈ N := (hmem s').mpr hs'
    rw [h] at hs'N
    exact hs'0 ((Submodule.mem_bot k).mp hs'N)
  have hT : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
  ext s s'
  have : s' ∈ N := by rw [hT]; trivial
  exact (hmem s').mp this s

end S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
end P2MW
export P2MW.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero (solution)

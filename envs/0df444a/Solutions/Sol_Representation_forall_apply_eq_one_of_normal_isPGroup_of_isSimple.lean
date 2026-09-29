-- Prove2me | solution 1 for Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/244b2595-9433-58ce-bf6d-29a92f67f925

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple

set_option autoImplicit false
universe u
open Module
open scoped IntermediateField Pointwise

set_option maxHeartbeats 1600000 in
theorem solution
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k] [CharP k p]
    {Δ : Type*} [Group Δ] [Finite Δ] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Δ V) (hV : Module.finrank k V ≠ 0)
    (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup Δ) [P.Normal] (hP : IsPGroup p P) :
    ∀ x ∈ P, ρ x = 1 := by
  classical

  let W : Submodule k V :=
    { carrier := {v | ∀ x : P, ρ x v = v}
      zero_mem' := fun x => map_zero _
      add_mem' := fun {a b} ha hb x => by rw [map_add, ha x, hb x]
      smul_mem' := fun c {a} ha x => by rw [map_smul, ha x] }
  have hWmem : ∀ v, v ∈ W ↔ ∀ x : P, ρ x v = v := fun _ => Iff.rfl
  have hWstab : ∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W := by
    intro d v hv
    rw [hWmem] at hv ⊢
    intro x

    have hmem : d⁻¹ * (x : Δ) * d ∈ P := by
      have := ‹P.Normal›.conj_mem (x : Δ) x.2 d⁻¹
      simpa using this
    have := hv ⟨_, hmem⟩

    calc ρ x (ρ d v) = ρ d (ρ (d⁻¹ * x * d) v) := by
            rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2; group
      _ = ρ d v := by rw [this]

  haveI : Finite V := Module.finite_of_finite k
  letI : MulAction P V := MulAction.compHom V ((ρ : Δ →* Module.End k V).comp P.subtype)
  have hsmul : ∀ (x : P) (v : V), x • v = ρ x v := fun _ _ => rfl
  have hmod := hP.card_modEq_card_fixedPoints V

  have hcardV : Nat.card V ≡ 0 [MOD p] := by
    classical
    haveI : Fintype k := Fintype.ofFinite k
    haveI : Fintype V := Fintype.ofFinite V
    obtain ⟨n, hp, hk⟩ := FiniteField.card k p
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k), hk, ← pow_mul, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self p (Nat.mul_ne_zero n.ne_zero hV)
  have hfix : Nat.card (MulAction.fixedPoints P V) ≡ 0 [MOD p] := hmod.symm.trans hcardV

  have hex : ∃ v : V, v ≠ 0 ∧ ∀ x : P, ρ x v = v := by
    by_contra hne
    push_neg at hne
    have hsub : ∀ v : MulAction.fixedPoints P V, v = ⟨0, fun x => by rw [hsmul, map_zero]⟩ := by
      rintro ⟨v, hv⟩
      by_contra h
      have hv0 : v ≠ 0 := fun h0 => h (Subtype.ext h0)
      obtain ⟨x, hx⟩ := hne v hv0
      exact hx (hv x)
    haveI : Subsingleton (MulAction.fixedPoints P V) := ⟨fun a b => by rw [hsub a, hsub b]⟩
    have h1 : Nat.card (MulAction.fixedPoints P V) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, ⟨⟨0, fun x => by rw [hsmul, map_zero]⟩⟩⟩
    rw [h1, Nat.modEq_zero_iff_dvd] at hfix
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hfix)
  obtain ⟨v, hv0, hv⟩ := hex
  have hWtop : W = ⊤ := by
    rcases hsimple W hWstab with h | h
    · exfalso
      have : v ∈ W := hv
      rw [h] at this
      exact hv0 ((Submodule.mem_bot k).mp this)
    · exact h
  intro x hx
  apply LinearMap.ext
  intro w
  have hw : w ∈ W := by rw [hWtop]; trivial
  exact hw ⟨x, hx⟩

end S_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple
end P2MW
export P2MW.S_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple (solution)

-- Prove2me | solution 1 for PadicAlgCl.exists_root_one_add_prime_forall_inertia_residual_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/657e1943-bf7f-5659-9453-d60aa906102c

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_root_one_add_prime_forall_inertia_residual_trivial

set_option autoImplicit false

namespace PadicAlgCl
namespace UFINAux
p2m_open "PadicAlgCl"

theorem one_add_prime_ne_zero (p : ℕ) [Fact p.Prime] : (1 + p : PadicAlgCl p) ≠ 0 := by
  have h : ((1 + p : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at h
  exact h

theorem eq_zero_of_forall_addMonoidHom_zmod_eq_zero (p : ℕ) [Fact p.Prime] {k : Type} [Field k]
    [CharP k p] (c : k) (h : ∀ Λ : k →+ ZMod p, Λ c = 0) : c = 0 := by
  letI := ZMod.algebra k p
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod p) c).mp fun φ => h φ.toAddMonoidHom

end PadicAlgCl.UFINAux

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (hzI : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1)
    (hcyc : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)})
    (η : B) (hη : IsUnit η) (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ p)
    (hall : ∀ Λ : IsLocalRing.ResidueField B →+ ZMod p,
      ∃ (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ),
        algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p ∧
        (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p)) ∧
        (p : ℤ) ∣ Padic.valuation (a : ℚ_[p]))
    (hU : ∀ c : ℚ_[p], c ≠ 0 → (p : ℤ) ∣ Padic.valuation c →
      ∃ (r : ℕ) (w : ℚ_[p]), c = (1 + (p : ℚ_[p])) ^ r * w ^ p) :
    ∃ β : PadicAlgCl p, β ^ p = 1 + (p : PadicAlgCl p) ∧
      ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          (x τ : B) - 1 ∈ IsLocalRing.maximalIdeal B ∧ y τ ∈ IsLocalRing.maximalIdeal B ∧
            (z τ : B) = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (1 + p : PadicAlgCl p) (Fact.out : p.Prime).pos
  have hβ0 : β ≠ 0 := by
    intro h0
    apply PadicAlgCl.UFINAux.one_add_prime_ne_zero p
    rw [← hβ, h0, zero_pow (Fact.out : p.Prime).ne_zero]
  refine ⟨β, hβ, fun τ hτI hτξ hτβ => ?_⟩

  have hz1 : z τ = 1 := hzI τ hτI

  have hx1 : (x τ : B) - 1 ∈ IsLocalRing.maximalIdeal B := by
    have h := hcyc τ 1 1 (fun μ hμ => by rw [pow_one]; exact hτξ μ (by rw [← hμ, pow_one]))
    rw [hz1, Units.val_one, mul_one, Nat.cast_one, pow_one] at h
    exact (Ideal.span_singleton_le_iff_mem _).mpr hpB h
  refine ⟨hx1, ?_, by rw [hz1, Units.val_one]⟩

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField B) = 0 := by
    rw [← map_natCast (IsLocalRing.residue B), IsLocalRing.residue_eq_zero_iff]
    exact hpB
  haveI : CharP (IsLocalRing.ResidueField B) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpk
  have hΛ : ∀ Λ : IsLocalRing.ResidueField B →+ ZMod p,
      Λ (IsLocalRing.residue B (η * y τ)) = 0 := by
    intro Λ
    obtain ⟨a, α, haα, hrep, hval⟩ := hall Λ

    obtain ⟨r, w, hrw⟩ := hU (a : ℚ_[p]) a.ne_zero hval
    have hw0 : w ≠ 0 := by
      intro hw
      apply a.ne_zero
      rw [hrw, hw, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero]
    set γ : PadicAlgCl p := β ^ r * algebraMap ℚ_[p] (PadicAlgCl p) w with hγdef
    have hγ0 : γ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hβ0) ((map_ne_zero _).mpr hw0)
    have hγp : γ ^ p = (α : PadicAlgCl p) ^ p := by
      rw [← haα, hrw, map_mul, map_pow, map_pow, map_add, map_one, map_natCast, hγdef, mul_pow,
        ← pow_mul, mul_comm r p, pow_mul, hβ]
    have hτγ : τ γ = γ := by
      rw [hγdef, map_mul, map_pow, hτβ, AlgEquiv.commutes]
    have hξ : ((α : PadicAlgCl p) * γ⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, hγp, mul_inv_cancel₀ (pow_ne_zero _ α.ne_zero)]
    have hτα : τ (α : PadicAlgCl p) = α := by
      have key : τ ((α : PadicAlgCl p) * γ⁻¹ * γ) = (α : PadicAlgCl p) * γ⁻¹ * γ := by
        rw [map_mul, hτξ _ hξ, hτγ]
      rwa [mul_assoc, inv_mul_cancel₀ hγ0, mul_one] at key

    have hm := hrep τ
    rw [hτα, hz1, inv_one, Units.val_one, mul_one] at hm
    have hζm : ζ ^ (Λ (IsLocalRing.residue B (η * y τ))).val = 1 :=
      (mul_eq_right₀ α.ne_zero).mp hm.symm
    have hdvd : p ∣ (Λ (IsLocalRing.residue B (η * y τ))).val := (hζ.pow_eq_one_iff_dvd _).mp hζm
    exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
  have hres : IsLocalRing.residue B (η * y τ) = 0 :=
    PadicAlgCl.UFINAux.eq_zero_of_forall_addMonoidHom_zmod_eq_zero p _ hΛ
  rw [IsLocalRing.residue_eq_zero_iff, Ideal.unit_mul_mem_iff_mem _ hη] at hres
  exact hres

end S_PadicAlgCl_exists_root_one_add_prime_forall_inertia_residual_trivial
end P2MW
export P2MW.S_PadicAlgCl_exists_root_one_add_prime_forall_inertia_residual_trivial (solution)

-- Prove2me | solution 1 for ValuationSubring.exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d85786b8-aea2-5b8c-a5c6-23cf987ec973

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq

set_option autoImplicit false

namespace TameExpAux

open IsLocalRing Polynomial

variable {L : Type} [Field L] (A : ValuationSubring L)

theorem mem_of_pow_eq_one {ω : L} {n : ℕ} (hn : n ≠ 0) (h : ω ^ n = 1) : ω ∈ A := by
  rcases A.mem_or_inv_mem ω with h1 | h1
  · exact h1
  · have hω0 : ω ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at h
      exact zero_ne_one h
    have h2 : ω * ω ^ (n - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), h]
    have key : ω = (ω ^ (n - 1))⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [key, ← inv_pow]
    exact pow_mem h1 _

theorem eq_one_of_pow_eq_one_of_residue_eq_one {n : ℕ} (hn : ((n : ℕ) : ResidueField A) ≠ 0)
    {η : L} (hη : η ^ n = 1) (hηA : η ∈ A) (hres : residue A ⟨η, hηA⟩ = 1) : η = 1 := by
  by_contra hne
  have hsum : (∑ i ∈ Finset.range n, (⟨η, hηA⟩ : A) ^ i) = 0 := by
    have h1 : ((⟨η, hηA⟩ : A) - 1) * ∑ i ∈ Finset.range n, (⟨η, hηA⟩ : A) ^ i = 0 := by
      rw [mul_geom_sum, sub_eq_zero]
      exact Subtype.ext (by simpa using hη)
    refine (mul_eq_zero.mp h1).resolve_left ?_
    intro h
    apply hne
    have h' := congrArg Subtype.val (sub_eq_zero.mp h)
    simpa using h'
  have h2 := congrArg (residue A) hsum
  rw [map_sum, map_zero] at h2
  simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h2
  exact hn h2

end TameExpAux

open TameExpAux IsLocalRing Polynomial in

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (ζ : ℕ → L) (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (π : L) (hπ0 : π ≠ 0)
    (σ : L ≃+* L) (hσπ : σ π = π)
    (hσres : ∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) :
    ∃ t : ℤ_[ℓ], (∀ (k : ℕ) (r : L), r ^ (ℓ ^ k) = π → σ r = ζ k ^ (t.appr k) * r) ∧
      (IsUnit t ↔ ∃ r : L, r ^ ℓ = π ∧ σ r ≠ r) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hℓ0 : ((ℓ : ℕ) : ResidueField A) ≠ 0 := hℓ.ne_zero
  have hℓk0 : ∀ k : ℕ, ((ℓ ^ k : ℕ) : ResidueField A) ≠ 0 := fun k => by
    rw [Nat.cast_pow]; exact pow_ne_zero k hℓ0
  have hpk : ∀ k : ℕ, ℓ ^ k ≠ 0 := fun k => pow_ne_zero k hℓp.ne_zero

  have hfix : ∀ (k : ℕ) (ω : L), ω ^ (ℓ ^ k) = 1 → σ ω = ω := by
    intro k ω hω
    have hω0 : ω ≠ 0 := by
      rintro rfl; rw [zero_pow (hpk k)] at hω; exact zero_ne_one hω
    have hωA : ω ∈ A := mem_of_pow_eq_one A (hpk k) hω
    have hσω : (σ ω) ^ (ℓ ^ k) = 1 := by rw [← map_pow, hω, map_one]
    have hσωA : σ ω ∈ A := mem_of_pow_eq_one A (hpk k) hσω
    have hωi : (ω⁻¹) ^ (ℓ ^ k) = 1 := by rw [inv_pow, hω, inv_one]
    have hωiA : ω⁻¹ ∈ A := mem_of_pow_eq_one A (hpk k) hωi
    have hη : (σ ω * ω⁻¹) ^ (ℓ ^ k) = 1 := by rw [mul_pow, hσω, hωi, one_mul]
    have hηA : σ ω * ω⁻¹ ∈ A := mul_mem hσωA hωiA
    have hres : residue A ⟨σ ω * ω⁻¹, hηA⟩ = 1 := by
      have e1 : (⟨σ ω * ω⁻¹, hηA⟩ : A) = ⟨σ ω, hσωA⟩ * ⟨ω⁻¹, hωiA⟩ := rfl
      have e2 : (⟨ω, hωA⟩ : A) * ⟨ω⁻¹, hωiA⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hω0)
      rw [e1, map_mul, hσres ⟨ω, hωA⟩ hσωA, ← map_mul, e2, map_one]
    have h1 := eq_one_of_pow_eq_one_of_residue_eq_one A (hℓk0 k) hη hηA hres
    calc σ ω = σ ω * ω⁻¹ * ω := by rw [mul_assoc, inv_mul_cancel₀ hω0, mul_one]
      _ = ω := by rw [h1, one_mul]

  have hroot : ∀ k : ℕ, ∃ r : L, r ^ (ℓ ^ k) = π := fun k =>
    IsAlgClosed.exists_pow_nat_eq π (Nat.pos_of_ne_zero (hpk k))
  choose r hr using hroot
  have hr0 : ∀ k, r k ≠ 0 := fun k h => hπ0 (by rw [← hr k, h, zero_pow (hpk k)])
  have hu : ∀ k, (σ (r k) * (r k)⁻¹) ^ (ℓ ^ k) = 1 := fun k => by
    rw [mul_pow, inv_pow, ← map_pow, hr, hσπ, mul_inv_cancel₀ hπ0]
  have he : ∀ k, ∃ i : ℕ, i < ℓ ^ k ∧ ζ k ^ i = σ (r k) * (r k)⁻¹ := fun k =>
    (hζ k).eq_pow_of_pow_eq_one (hu k)
  choose e he_lt he_eq using he

  have hind : ∀ (k : ℕ) (r' : L), r' ^ (ℓ ^ k) = π → σ r' = ζ k ^ e k * r' := by
    intro k r' hr'
    have hω : (r' * (r k)⁻¹) ^ (ℓ ^ k) = 1 := by
      rw [mul_pow, inv_pow, hr', hr, mul_inv_cancel₀ hπ0]
    have hσω := hfix k _ hω
    rw [map_mul, map_inv₀] at hσω
    have hσr : σ (r k) = ζ k ^ e k * r k := by
      rw [he_eq, mul_assoc, inv_mul_cancel₀ (hr0 k), mul_one]
    have hσr0 : σ (r k) ≠ 0 := (map_ne_zero σ).mpr (hr0 k)

    calc σ r' = σ r' * (σ (r k))⁻¹ * σ (r k) := by rw [mul_assoc, inv_mul_cancel₀ hσr0, mul_one]
      _ = r' * (r k)⁻¹ * (ζ k ^ e k * r k) := by rw [hσω, hσr]
      _ = ζ k ^ e k * r' := by
          rw [mul_comm (ζ k ^ e k) (r k), ← mul_assoc, mul_assoc r', inv_mul_cancel₀ (hr0 k), mul_one,
            mul_comm]

  have hstep : ∀ k, (e (k + 1) : ZMod (ℓ ^ k)) = (e k : ZMod (ℓ ^ k)) := by
    intro k
    have h1 : ((r (k + 1)) ^ ℓ) ^ (ℓ ^ k) = π := by rw [← pow_mul, ← pow_succ', hr]
    have h2 := hind k _ h1
    have h3 := hind (k + 1) _ (hr (k + 1))
    have h4 : σ ((r (k + 1)) ^ ℓ) = ζ k ^ e (k + 1) * (r (k + 1)) ^ ℓ := by
      rw [map_pow, h3, mul_pow, ← pow_mul, mul_comm (e (k + 1)) ℓ, pow_mul, hζc]
    have h5 : ζ k ^ e (k + 1) = ζ k ^ e k := by
      have hne : (r (k + 1)) ^ ℓ ≠ 0 := pow_ne_zero _ (hr0 _)
      exact mul_right_cancel₀ hne (h4.symm.trans h2)
    have hζ0 : ζ k ≠ 0 := (hζ k).ne_zero (hpk k)
    have h6 : ζ k ^ ((e k : ℤ) - (e (k + 1) : ℤ)) = 1 := by
      rw [zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, ← h5, div_self (pow_ne_zero _ hζ0)]
    have h7 := ((hζ k).zpow_eq_one_iff_dvd _).mp h6
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.modEq_iff_dvd.mpr (by exact_mod_cast h7)
  have hcompat : ∀ k1 k2 : ℕ, k1 ≤ k2 → (e k2 : ZMod (ℓ ^ k1)) = (e k1 : ZMod (ℓ ^ k1)) := by
    intro k1 k2 hk
    induction k2, hk using Nat.le_induction with
    | base => rfl
    | succ k2 hk ih =>
        have h := congrArg (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))) (hstep k2)
        rw [map_natCast, map_natCast] at h
        exact h.trans ih

  let f : ∀ k : ℕ, Polynomial ℤ →+* ZMod (ℓ ^ k) := fun k => (Polynomial.aeval (R := ℤ) (e k : ZMod (ℓ ^ k))).toRingHom
  have hfX : ∀ k, f k X = (e k : ZMod (ℓ ^ k)) := fun k => by simp [f]
  have hfC : ∀ k (z : ℤ), f k (C z) = (z : ZMod (ℓ ^ k)) := fun k z => by simp [f]
  have hfc : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2), (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))).comp (f k2) = f k1 := by
    intro k1 k2 hk
    apply Polynomial.ringHom_ext
    · intro z; rw [RingHom.comp_apply, hfC, hfC, map_intCast]
    · rw [RingHom.comp_apply, hfX, hfX, map_natCast, hcompat k1 k2 hk]
  let t : ℤ_[ℓ] := PadicInt.lift hfc X
  have ht : ∀ k, PadicInt.toZModPow k t = (e k : ZMod (ℓ ^ k)) := fun k => by
    have := PadicInt.lift_spec hfc k
    rw [← hfX k, ← this]; rfl
  have happr : ∀ k, t.appr k = e k := by
    intro k
    have h1 : ((t.appr k : ℕ) : ZMod (ℓ ^ k)) = (e k : ZMod (ℓ ^ k)) := by rw [← ht k]; rfl
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (PadicInt.appr_lt t k), Nat.mod_eq_of_lt (he_lt k)] at h1
    exact h1
  refine ⟨t, fun k r' hr' => by rw [happr k]; exact hind k r' hr', ?_⟩

  have hunit : IsUnit t ↔ PadicInt.toZModPow 1 t ≠ 0 := by
    rw [← not_iff_not, not_not, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      PadicInt.maximalIdeal_eq_span_p, ← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one]
  have he1 : PadicInt.toZModPow 1 t ≠ 0 ↔ ζ 1 ^ e 1 ≠ 1 := by
    rw [ht 1]
    have hval : ((e 1 : ℕ) : ZMod (ℓ ^ 1)) = 0 ↔ e 1 = 0 := by
      rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (he_lt 1)]
    rw [ne_eq, hval]
    constructor
    · intro h0 h1
      exact h0 (Nat.eq_zero_of_dvd_of_lt ((hζ 1).dvd_of_pow_eq_one _ h1) (he_lt 1))
    · intro h1 h0
      exact h1 (by rw [h0, pow_zero])
  rw [hunit, he1]
  constructor
  · intro hne
    refine ⟨r 1, by simpa using hr 1, ?_⟩
    rw [hind 1 (r 1) (hr 1)]
    intro h
    apply hne
    exact mul_left_eq_self₀.mp h |>.resolve_right (hr0 1)
  · rintro ⟨r', hr', hσr'⟩ h1
    apply hσr'
    rw [hind 1 r' (by simpa using hr'), h1, one_mul]

end S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
end P2MW
export P2MW.S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq (solution)

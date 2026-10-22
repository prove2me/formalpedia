-- Prove2me | solution 1 for ScatPoly.Inequiv.card_H
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:48:37.076519+00:00
-- url     : https://prove2.me/submissions/2abc2a66-082a-4329-aa34-de3004f76c82

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

set_option autoImplicit false
open ScatPoly.Inequiv

theorem spi_card_H (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t)) :
    Nat.card (hSet F q t) = q ^ t + 1 := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = q ^ t := ⟨_, rfl⟩
  have hqodd : Odd q := by rw [hq]; exact hp.pow
  have hQodd : Odd Q := by rw [hQ]; exact hqodd.pow
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    rcases hp with ⟨c, hc⟩
    omega
  have hq3 : 3 ≤ q := by
    rw [hq]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) hr
  have hQ3 : 3 ≤ Q := by
    rw [hQ]
    calc 3 ≤ q := hq3
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ t := Nat.pow_le_pow_right (by omega) ht
  have hF : Fintype.card F = Q * Q := by rw [hcard, hQ, ← pow_two, ← pow_mul]; ring_nf
  have hN : Nat.card Fˣ = (Q - 1) * (Q + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hF]
    obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.sub_eq_of_eq_add]
    ring
  have hg1 : (Nat.card Fˣ).gcd (Q + 1) = Q + 1 := by
    apply Nat.gcd_eq_right
    rw [hN]; exact Dvd.intro_left _ rfl
  have hg2 : (Nat.card Fˣ).gcd (Q - 1) = Q - 1 := by
    apply Nat.gcd_eq_right
    rw [hN]; exact Dvd.intro _ rfl
  let φ : Fˣ →* Fˣ := powMonoidHom (Q + 1)
  let ψ : Fˣ →* Fˣ := powMonoidHom (Q - 1)
  have hrange : Nat.card φ.range = Q - 1 := by
    rw [IsCyclic.card_powMonoidHom_range, hg1, hN]
    exact Nat.mul_div_cancel _ (by omega)
  have hker : Nat.card ψ.ker = Q - 1 := by
    rw [IsCyclic.card_powMonoidHom_ker, hg2]
  have hle : φ.range ≤ ψ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [φ, ψ, powMonoidHom_apply]
    rw [← pow_mul, show (Q + 1) * (Q - 1) = Nat.card Fˣ by rw [hN, mul_comm]]
    exact pow_card_eq_one'
  have heq : φ.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hker])
  have hm1 : (-1 : Fˣ) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [ψ, powMonoidHom_apply]
    apply Even.neg_one_pow
    rcases hQodd with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  rw [← heq] at hm1
  obtain ⟨u0, hu0⟩ := hm1
  have hu0' : u0 ^ (Q + 1) = -1 := hu0
  -- count
  have hS : Nat.card {u : Fˣ // u ^ (Q + 1) = -1} = Nat.card φ.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun u => ⟨u.1 * u0⁻¹, by
          rw [MonoidHom.mem_ker]
          simp only [φ, powMonoidHom_apply]
          rw [mul_pow, u.2, inv_pow, hu0']
          simp⟩
        invFun := fun k => ⟨k.1 * u0, by
          have := k.2
          rw [MonoidHom.mem_ker] at this
          simp only [φ, powMonoidHom_apply] at this
          rw [mul_pow, this, hu0', one_mul]⟩
        left_inv := fun u => by ext; simp
        right_inv := fun k => by ext; simp }
  have hkercard : Nat.card φ.ker = Q + 1 := by
    rw [IsCyclic.card_powMonoidHom_ker, hg1]
  have hH : Nat.card (hSet F q t) = Nat.card {u : Fˣ // u ^ (Q + 1) = -1} := by
    apply Nat.card_congr
    have hne : ∀ x : F, x ^ (Q + 1) = -1 → x ≠ 0 := by
      intro x hx h0
      rw [h0, zero_pow (by omega)] at hx
      have : (1 : F) = 0 := by linear_combination hx
      exact one_ne_zero this
    exact
      { toFun := fun x => ⟨Units.mk0 x.1 (hne x.1 (by have := x.2; rw [hQ]; exact this)), by
          have := x.2
          apply Units.ext
          simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_neg, Units.val_one]
          rw [hQ]; exact this⟩
        invFun := fun u => ⟨u.1, by
          have := congrArg Units.val u.2
          simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this
          show (u.1 : F) ^ (q ^ t + 1) = -1
          rw [← hQ]; exact this⟩
        left_inv := fun x => by ext; simp
        right_inv := fun u => by ext; simp }
  rw [hH, hS, hkercard, hQ]

theorem solution (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t)) :
    Nat.card (hSet F q t) = q ^ t + 1 := spi_card_H F p r t q hp hr hq ht hcard

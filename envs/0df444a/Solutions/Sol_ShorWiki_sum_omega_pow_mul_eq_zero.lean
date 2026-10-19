-- Prove2me | solution 1 for ShorWiki.sum_omega_pow_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:36:05.628131+00:00
-- url     : https://prove2.me/submissions/19a1d0a8-2ec6-4ee2-9071-f82a30e5a818

import Mathlib
import Definitions.Def_ShorWiki_Defs
open ShorWiki

namespace ShorHelpers

lemma one_lt_N (N a : ℕ) (ha : 1 < a) (haN : a < N) : 1 < N := by omega

lemma ord_pos (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) :
    0 < ord N a := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  exact orderOf_pos _

lemma ord_le (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) :
    ord N a ≤ N := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  calc _ ≤ Fintype.card (ZMod N)ˣ := orderOf_le_card_univ
    _ = Nat.totient N := ZMod.card_units_eq_totient N
    _ ≤ N := Nat.totient_le N

lemma pow_ord (N a : ℕ) : (a : ZMod N) ^ ord N a = 1 := pow_orderOf_eq_one _

lemma dvd_iff_cast_sub (N x : ℕ) (hx : 1 ≤ x) : N ∣ x - 1 ↔ (x : ZMod N) = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hx, Nat.cast_one, sub_eq_zero]

lemma half_spec (N a : ℕ) (heven : Even (ord N a)) :
    ((a : ZMod N) ^ (ord N a / 2)) ^ 2 = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp heven), pow_ord]

lemma dvd_prod (N a : ℕ) (ha : 1 < a) (heven : Even (ord N a)) :
    N ∣ (a ^ (ord N a / 2) - 1) * (a ^ (ord N a / 2) + 1) := by
  have hx : 1 ≤ a ^ (ord N a / 2) := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hx]
  have := half_spec N a heven
  linear_combination this

lemma not_dvd_sub (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N)
    (heven : Even (ord N a)) : ¬ N ∣ a ^ (ord N a / 2) - 1 := by
  intro h
  have hx : 1 ≤ a ^ (ord N a / 2) := Nat.one_le_pow _ _ (by omega)
  rw [dvd_iff_cast_sub N _ hx, Nat.cast_pow] at h
  have hdvd : ord N a ∣ ord N a / 2 := orderOf_dvd_of_pow_eq_one h
  have hpos := ord_pos N a ha haN hcop
  have h2 : 0 < ord N a / 2 := by
    obtain ⟨k, hk⟩ := heven; omega
  have := Nat.le_of_dvd h2 hdvd
  omega

end ShorHelpers

theorem solution (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r - 1) :
    ∑ j ∈ Finset.range r, omega r ^ (j * k) = 0 := by
  have hr : r ≠ 0 := by omega
  have hprim : IsPrimitiveRoot (omega r) r := Complex.isPrimitiveRoot_exp r hr
  set x := omega r ^ k with hx
  have hx1 : x ≠ 1 := by
    intro h
    have := (hprim.pow_eq_one_iff_dvd k).mp h
    have := Nat.le_of_dvd (by omega) this
    omega
  have hxr : x ^ r = 1 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have e : ∑ j ∈ Finset.range r, omega r ^ (j * k) = ∑ j ∈ Finset.range r, x ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx, ← pow_mul, mul_comm]
  rw [e]
  have hg := geom_sum_mul x r
  rw [hxr, sub_self] at hg
  rcases mul_eq_zero.mp hg with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hx1

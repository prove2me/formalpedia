-- Prove2me | solution 1 for ShorWiki.not_dvd_pow_half_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:35:50.537905+00:00
-- url     : https://prove2.me/submissions/c8b30861-a20b-4313-aeb0-db8dbb5870ec

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

open ShorHelpers in
theorem solution (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (heven : Even (ord N a)) :
    ¬ N ∣ a ^ (ord N a / 2) - 1 :=
  not_dvd_sub N a ha haN hcop heven

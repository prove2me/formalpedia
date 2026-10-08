-- Prove2me | solution 1 for OddPerfectNumber.Kernel.geom_sum_congr_one_mod_p_val_eq_val_of_two_e_plus_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:07:18.545221+00:00
-- url     : https://prove2.me/submissions/a6835da7-deb4-49ad-8d0b-e310ba09d65c

import Mathlib

set_option autoImplicit false

theorem solution (p t e : Nat)
    (hp : p.Prime) (hpt : Not (Dvd.dvd p t)) (ht1 : t % p = 1) :
    ((∑ i ∈ Finset.range (2 * e + 1), t ^ i)).factorization p = (2 * e + 1).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  have hp1 : 1 < p := hp.one_lt
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht1
  by_cases htone : t = 1
  · subst htone
    simp
  have ht2 : 2 ≤ t := by omega
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    have hS : (∑ i ∈ Finset.range (2 * e + 1), t ^ i) % 2 = 1 := by
      rw [Finset.sum_nat_mod]
      have : ∀ i ∈ Finset.range (2 * e + 1), t ^ i % 2 = 1 := by
        intro i _
        rw [Nat.pow_mod, ht1]
        simp
      rw [Finset.sum_congr rfl this]
      simp
    have hn : (2 * e + 1) % 2 = 1 := by omega
    rw [padicValNat.eq_zero_of_not_dvd (by omega), padicValNat.eq_zero_of_not_dvd (by omega)]
  · obtain ⟨x, rfl⟩ : ∃ x, t = x + 1 := ⟨t - 1, by omega⟩
    have hx0 : x ≠ 0 := by omega
    have hgeom := geom_sum_mul_add x (2 * e + 1)
    set S := ∑ i ∈ Finset.range (2 * e + 1), (x + 1) ^ i with hSdef
    have hS0 : S ≠ 0 := by
      intro h
      rw [h] at hgeom
      simp at hgeom
      have : 1 < (x + 1) ^ (2 * e + 1) := Nat.one_lt_pow (by omega) (by omega)
      omega
    have hdx : p ∣ x := by
      have : (x + 1) % p = 1 % p := by rw [ht1, Nat.mod_eq_of_lt hp1]
      have h := (Nat.ModEq.add_right_cancel' 1 this)
      exact Nat.modEq_zero_iff_dvd.mp h
    have key := padicValNat.pow_sub_pow (p := p) hodd (x := x + 1) (y := 1) (by omega)
      (by simpa using hdx) hpt (n := 2 * e + 1) (by omega)
    rw [one_pow, ← hgeom, Nat.add_sub_cancel, padicValNat.mul hS0 hx0, Nat.add_sub_cancel] at key
    omega

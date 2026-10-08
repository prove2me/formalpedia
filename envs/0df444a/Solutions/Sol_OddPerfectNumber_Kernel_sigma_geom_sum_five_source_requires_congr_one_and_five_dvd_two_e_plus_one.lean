-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_geom_sum_five_source_requires_congr_one_and_five_dvd_two_e_plus_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:42:17.73566+00:00
-- url     : https://prove2.me/submissions/4a732d9e-80be-4391-af99-fd76d3805ed3

import Mathlib

set_option autoImplicit false

lemma OPN66c4323c_aux (x : ZMod 5) (hx : x ≠ 0) (e : Nat) (h : x ^ (2 * e + 1) = 1) : x = 1 := by
  have h4 : x ^ 4 = 1 := by
    clear h; revert hx; revert x; decide
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  · subst hk
    have : x ^ (2 * (2 * k) + 1) = (x ^ 4) ^ k * x := by ring
    rw [this, h4, one_pow, one_mul] at h
    exact h
  · subst hk
    have : x ^ (2 * (2 * k + 1) + 1) = (x ^ 4) ^ k * x ^ 3 := by ring
    rw [this, h4, one_pow, one_mul] at h
    clear this h4
    revert hx h
    revert x
    decide

theorem solution (t e : Nat)
    (ht : t.Prime) (ht5 : Not (Dvd.dvd 5 t))
    (h : Dvd.dvd 5 (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t % 5 = 1 \/ 5 % (2 * e + 1) = 0) := by
  left
  have hx : ((t : ℕ) : ZMod 5) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact ht5
  have hs : (∑ i ∈ Finset.range (2 * e + 1), ((t : ℕ) : ZMod 5) ^ i) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ 5).mpr h
    push_cast at this
    exact this
  have hp : ((t : ℕ) : ZMod 5) ^ (2 * e + 1) = 1 := by
    have := geom_sum_mul ((t : ℕ) : ZMod 5) (2 * e + 1)
    rw [hs, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have h1 := OPN66c4323c_aux _ hx e hp
  have := congrArg ZMod.val h1
  rw [ZMod.val_natCast] at this
  exact this.trans rfl

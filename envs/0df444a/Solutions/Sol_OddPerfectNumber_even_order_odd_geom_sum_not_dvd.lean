-- Prove2me | solution 1 for OddPerfectNumber.even_order_odd_geom_sum_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:56:19.467518+00:00
-- url     : https://prove2.me/submissions/9295b762-1704-467f-8570-e4a636b2bbd7

import Mathlib

theorem solution (b p n : Nat) (heven : Even (orderOf (b : ZMod p)))
    (hodd : Odd n) : ¬ (p ∣ (Finset.range n).sum (fun i => b ^ i)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · intro hdvd
    rw [Nat.zero_dvd] at hdvd
    obtain ⟨k, hk⟩ := hodd
    have hmem : (0 : Nat) ∈ Finset.range n := by rw [hk]; simp
    have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (b ^ i)) hmem
    rw [pow_zero] at hle
    omega
  · haveI : NeZero p := ⟨hpos.ne'⟩
    intro hdvd
    have hS0 : ((Finset.range n).sum (fun i => (b : ZMod p) ^ i)) = 0 := by
      have h1 : (((Finset.range n).sum (fun i => b ^ i) : Nat) : ZMod p) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd
      push_cast at h1
      exact h1
    have hgeom : ((Finset.range n).sum (fun i => (b : ZMod p) ^ i)) * ((b : ZMod p) - 1)
        = (b : ZMod p) ^ n - 1 :=
      geom_sum_mul _ _
    rw [hS0, zero_mul] at hgeom
    have hpow : (b : ZMod p) ^ n = 1 := by
      have h := hgeom.symm
      rwa [sub_eq_zero] at h
    have hordvd : orderOf (b : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨r, hr⟩ := heven
    obtain ⟨t, ht⟩ := hordvd
    have hevn : Even n := ⟨r * t, by rw [ht, hr]; ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) hevn

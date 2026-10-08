-- Prove2me | solution 1 for OddPerfectNumber.Kernel.fourth_power_residue_of_geom_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:26:28.557983+00:00
-- url     : https://prove2.me/submissions/936ca3ee-c86e-46f7-9587-d0146b13fa82

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd
import Theorems.Thm_OddPerfectNumber_Kernel_odd_order_dvd_quarter_of_p_minus_one

theorem solution (p t e : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (ht : t.Prime) (hpt : Not (Dvd.dvd p t))
    (hsrc : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t ^ ((p - 1) / 4)) % p = 1 := by
  have hord := OddPerfectNumber.geom_sum_dvd_implies_order_dvd hsrc
  have hodd : Odd (orderOf (t : ZMod p)) := by
    obtain ⟨j, hj⟩ := hord
    have h21 : Odd (2 * e + 1) := ⟨e, rfl⟩
    rw [hj] at h21
    exact (Nat.odd_mul.mp h21).1
  have hquarter := OddPerfectNumber.Kernel.odd_order_dvd_quarter_of_p_minus_one
    hp hp4 hpt hodd
  have hpow : (t : ZMod p) ^ ((p - 1) / 4) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hquarter
  have hp2 : 2 ≤ p := hp.two_le
  haveI : NeZero p := ⟨by omega⟩
  have h1mod : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt (by omega)
  have hcast : ((t ^ ((p - 1) / 4) : Nat) : ZMod p) = ((1 : Nat) : ZMod p) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hpow
  have hmod : t ^ ((p - 1) / 4) ≡ 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hmod2 : (t ^ ((p - 1) / 4)) % p = 1 % p := hmod
  rw [h1mod] at hmod2
  exact hmod2

-- Prove2me | solution 1 for PadicInt.dvd_of_one_add_prime_pow_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/23f6ae4f-ef8e-5c1e-9c27-c03af641605d

import Mathlib
import Theorems.Thm_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_dvd_of_one_add_prime_pow_eq_pow

open Polynomial

namespace Ws26U4

theorem exists_one_add_pow_eq_cubic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ d : R, (1 + x) ^ n = 1 + n * x + (n.choose 2 : R) * x ^ 2 + x ^ 3 * d := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(n.choose 2 : R) + d + x * d, ?_⟩
    rw [pow_succ, hd, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    ring

theorem exists_one_add_pow_eq_quadratic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  obtain ⟨d, hd⟩ := exists_one_add_pow_eq_cubic x n
  exact ⟨(n.choose 2 : R) + x * d, by rw [hd]; ring⟩

end Ws26U4

namespace Ws26U4

section IntBasic
open PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem toZMod_natCast_self : toZMod (p : ℤ_[p]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

theorem toZModPow_natCast_self_pow (n : ℕ) : toZModPow n ((p : ℤ_[p]) ^ n) = 0 := by
  rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]

theorem norm_eq_one_of_toZMod_ne_zero {z : ℤ_[p]} (hz : toZMod z ≠ 0) : ‖z‖ = 1 := by
  rcases lt_or_eq_of_le (norm_le_one z) with h | h
  · exfalso
    apply hz
    rw [← RingHom.mem_ker, ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits]
    exact h
  · exact h

theorem norm_eq_one_of_toZMod_eq_one {z : ℤ_[p]} (hz : toZMod z = 1) : ‖z‖ = 1 :=
  norm_eq_one_of_toZMod_ne_zero (by rw [hz]; exact one_ne_zero)

theorem exists_eq_one_add_prime_mul_of_toZMod_eq_one {z : ℤ_[p]} (hz : toZMod z = 1) :
    ∃ b : ℤ_[p], z = 1 + p * b := by
  have hker : z - 1 ∈ RingHom.ker (toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, hz, map_one, sub_self]
  rw [ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  exact ⟨b, by rw [← hb]; ring⟩

theorem exists_eq_one_add_prime_sq_mul_of_toZModPow_two_eq_one {u : ℤ_[p]}
    (hu : toZModPow 2 u = 1) : ∃ b : ℤ_[p], u = 1 + (p : ℤ_[p]) ^ 2 * b := by
  have hker : u - 1 ∈ RingHom.ker (toZModPow (p := p) 2) := by
    rw [RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  rw [ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  exact ⟨b, by rw [← hb]; ring⟩

theorem toZMod_one_add_prime : toZMod (1 + p : ℤ_[p]) = 1 := by
  rw [map_add, map_one, toZMod_natCast_self, add_zero]

theorem toZModPow_two_one_add_prime_pow (j : ℕ) :
    toZModPow 2 ((1 + p : ℤ_[p]) ^ j) = 1 + (j : ZMod (p ^ 2)) * p := by
  obtain ⟨c, hc⟩ := exists_one_add_pow_eq_quadratic (p : ℤ_[p]) j
  rw [hc, map_add, map_add, map_mul, map_one, map_mul, map_natCast, map_natCast,
    toZModPow_natCast_self_pow, zero_mul, add_zero]

end IntBasic

end Ws26U4

open Ws26U4 PadicInt in
theorem solution {p : ℕ} [hp : Fact p.Prime]
    {j : ℕ} {z : ℤ_[p]} (h : (1 + p : ℤ_[p]) ^ j = z ^ p) : p ∣ j := by

  have hz1 : toZMod z = 1 := by
    have h' := congrArg toZMod h
    rw [map_pow, toZMod_one_add_prime, one_pow, map_pow, ZMod.pow_card] at h'
    exact h'.symm

  have h2 := PadicInt.toZModPow_two_pow_eq_one_of_toZMod_eq_one hz1
  rw [← h, toZModPow_two_one_add_prime_pow, add_eq_left, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff, pow_two] at h2
  exact Nat.dvd_of_mul_dvd_mul_right hp.out.pos h2

end S_PadicInt_dvd_of_one_add_prime_pow_eq_pow
end P2MW
export P2MW.S_PadicInt_dvd_of_one_add_prime_pow_eq_pow (solution)

-- Prove2me | solution 1 for PadicInt.exists_pow_eq_of_toZModPow_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/75a59f96-6f7b-53a5-bbc5-1d577a993123

import Mathlib
import Theorems.Thm_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one

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

namespace Ws26U4
section IntOddCong
open PadicInt
variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_one_add_prime_mul_pow_prime_eq (hp2 : p ≠ 2) (b : ℤ_[p]) :
    ∃ e : ℤ_[p], (1 + p * b) ^ p = 1 + (p : ℤ_[p]) ^ 2 * b + (p : ℤ_[p]) ^ 3 * e := by
  obtain ⟨d, hd⟩ := exists_one_add_pow_eq_cubic ((p : ℤ_[p]) * b) p
  have h2p : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  obtain ⟨m, hm⟩ := hp.out.dvd_choose_self (k := 2) two_ne_zero h2p
  refine ⟨(m : ℤ_[p]) * b ^ 2 + b ^ 3 * d, ?_⟩
  rw [hd, hm, Nat.cast_mul]
  ring

end IntOddCong
end Ws26U4

open Ws26U4 PadicInt in
theorem solution {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {u : ℤ_[p]} (hu : PadicInt.toZModPow 2 u = 1) :
    ∃ z : ℤ_[p], PadicInt.toZMod z = 1 ∧ z ^ p = u := by
  obtain ⟨b, hb⟩ := exists_eq_one_add_prime_sq_mul_of_toZModPow_two_eq_one hu
  obtain ⟨e, he⟩ := exists_one_add_prime_mul_pow_prime_eq hp2 b

  have hu1 : toZMod u = 1 := by
    rw [hb, map_add, map_one, map_mul, map_pow, toZMod_natCast_self, zero_pow two_ne_zero,
      zero_mul, add_zero]
  have hu_norm : ‖u‖ = 1 := norm_eq_one_of_toZMod_eq_one hu1

  have hres : ∃ c : ZMod (p ^ 3), c ^ p = toZModPow 3 u := by
    refine ⟨toZModPow 3 (1 + p * b), ?_⟩
    rw [← map_pow, he, hb, map_add, map_mul (toZModPow 3) ((p : ℤ_[p]) ^ 3),
      toZModPow_natCast_self_pow, zero_mul, add_zero]
  obtain ⟨z, hz⟩ := PadicInt.exists_pow_eq_of_exists_pow_eq_toZModPow_three hu_norm hres
  refine ⟨z, ?_, hz⟩

  rw [← ZMod.pow_card (toZMod z), ← map_pow, hz, hu1]

end S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one
end P2MW
export P2MW.S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one (solution)

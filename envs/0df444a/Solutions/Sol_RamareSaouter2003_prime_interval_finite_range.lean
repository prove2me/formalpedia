-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_finite_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:01:18.42014+00:00
-- url     : https://prove2.me/submissions/923ab471-e4e5-49ec-8e3a-557d3f9b494b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RamareSaouter2003_prime_interval_finite_range_nat_strict_upper
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (x : Real) (hx : 10726905041 < x)
    (hupper : x < 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      x * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) <= x := by
  let n := Nat.floor x + 1
  have hxpos : 0 <= x := by linarith
  have hfloor : (Nat.floor x : Real) <= x := Nat.floor_le hxpos
  have hxlt : x < (n : Real) := by
    simpa [n] using Nat.lt_floor_add_one x
  have hnlow_real : (10726905041 : Real) < (n : Real) := by linarith
  have hnlow : 10726905041 < n := by exact_mod_cast hnlow_real
  have hnupper : n <= 10 ^ (20 : Nat) := by
    by_contra h
    have hnat : 10 ^ (20 : Nat) < n := Nat.lt_of_not_ge h
    change 10 ^ (20 : Nat) < Nat.floor x + 1 at hnat
    have hfloorbound_nat : 10 ^ (20 : Nat) <= Nat.floor x := by omega
    have hfloorbound : (10 ^ (20 : Nat) : Real) <= (Nat.floor x : Real) := by exact_mod_cast hfloorbound_nat
    linarith
  have hex := RamareSaouter2003.prime_interval_finite_range_nat_strict_upper n hnlow hnupper
  let p := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hp : p.Prime := hspec.1
  have hplower : (n : Real) * (1 - 1 / 28314000) < (p : Real) := hspec.2.1
  have hpupper : (p : Real) < (n : Real) := hspec.2.2
  have hlower : x * (1 - 1 / 28314000) < (p : Real) := by
    have hfactor : 0 < (1 : Real) - 1 / 28314000 := by norm_num
    have hmul := mul_lt_mul_of_pos_right hxlt hfactor
    simpa [n] using hmul.trans hplower
  have hpNat : p <= Nat.floor x := by
    have hcast : p < Nat.floor x + 1 := by exact_mod_cast hpupper
    omega
  have hpReal : (p : Real) <= (Nat.floor x : Real) := by exact_mod_cast hpNat
  have hupper' : (p : Real) <= x := hpReal.trans hfloor
  exact Exists.intro p (And.intro hp (And.intro hlower hupper'))
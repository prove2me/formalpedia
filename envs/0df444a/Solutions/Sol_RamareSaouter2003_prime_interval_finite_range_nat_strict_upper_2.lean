-- Prove2me | solution 2 for RamareSaouter2003.prime_interval_finite_range_nat_strict_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:04:18.645749+00:00
-- url     : https://prove2.me/submissions/58aceacc-6264-463a-bab2-d5bbe3a751e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RamareSaouter2003_prime_interval_finite_range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic

theorem solution (n : Nat) (hn : 10726905041 < n)
    (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\
      (p : Real) < (n : Real) := by
  let q : Nat := n / 28314000
  let r : Nat := n % 28314000
  let m : Nat := n - q - 1
  have hnqr : n = q * 28314000 + r := by
    dsimp [q, r]
    omega
  have hrlt : r < 28314000 := Nat.mod_lt _ (by norm_num)
  have hnm : m + q + 1 = n := by
    dsimp [m, q]
    omega
  have hnqrR : (n : Real) = (q : Real) * 28314000 + (r : Real) := by
    exact_mod_cast hnqr
  have hnmR : (m : Real) + (q : Real) + 1 = (n : Real) := by
    exact_mod_cast hnm
  have hrltR : (r : Real) < 28314000 := by exact_mod_cast hrlt
  by_cases hrzero : r = 0
  · have hfinite := RamareSaouter2003.prime_interval_finite_range
      (n : Real) (by exact_mod_cast hn)
      (by exact_mod_cast (lt_of_le_of_ne hupper (by
        intro heq
        have hnEq : n = 10 ^ (20 : Nat) := by exact_mod_cast heq
        have hrzero' : n % 28314000 = 0 := by simpa [r] using hrzero
        rw [hnEq] at hrzero'
        norm_num at hrzero'
        )))
    obtain ⟨p, hp, hplower, hpupper⟩ := hfinite
    have hpupperN : p <= n := by exact_mod_cast hpupper
    have hpne : p ≠ n := by
      intro hpn
      subst p
      have hprime : n.Prime := hp
      have hdiv : 28314000 ∣ n := by
        have hrzero' : n % 28314000 = 0 := by simpa [r] using hrzero
        exact Nat.dvd_of_mod_eq_zero hrzero'
      have hcases := hprime.eq_one_or_self_of_dvd 28314000 hdiv
      have hbig : 28314000 < n := by omega
      omega
    have hpupperN' : p < n := by omega
    refine ⟨p, And.intro hp (And.intro hplower ?_)⟩
    exact_mod_cast hpupperN'
  · let x : Real := (n : Real) - 1 / (2 * 28314000)
    have hxlow : (10726905041 : Real) < x := by
      dsimp [x]
      have hdelta : (0 : Real) < 1 / (2 * 28314000) := by norm_num
      have hdeltaLt : (1 : Real) / (2 * 28314000) < 1 := by norm_num
      have hnNat : 10726905042 <= n := by omega
      have hnR : (10726905042 : Real) <= (n : Real) := by exact_mod_cast hnNat
      linarith
    have hxupper : x < (10 ^ (20 : Nat) : Real) := by
      dsimp [x]
      have hdelta : (0 : Real) < 1 / (2 * 28314000) := by norm_num
      have hcast : (n : Real) <= (10 ^ (20 : Nat) : Real) := by exact_mod_cast hupper
      linarith
    have hfinite := RamareSaouter2003.prime_interval_finite_range x hxlow hxupper
    obtain ⟨p, hp, hplower, hpupper⟩ := hfinite
    have hmlower : (m : Real) < x * (1 - 1 / 28314000) := by
      dsimp [x]
      have hdeltaD : (1 : Real) / (2 * 28314000) < 1 / 28314000 := by norm_num
      have hrle : r <= 28313999 := by omega
      have hrleR : (r : Real) <= 28313999 := by exact_mod_cast hrle
      have hsum : (r : Real) + 28314000 * (1 / (2 * 28314000 : Real)) < 28314000 := by
        norm_num at hdeltaD ⊢
        nlinarith [hrleR, hdeltaD]
      field_simp
      nlinarith [hnqrR, hnmR, hrltR, hrleR, hdeltaD, hsum]
    have hmp : m < p := by
      have : (m : Real) < (p : Real) := hmlower.trans hplower
      exact_mod_cast this
    have htarget : (n : Real) * (1 - 1 / 28314000) < (m : Real) + 1 := by
      have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
      have hrposR : (0 : Real) < (r : Real) := by exact_mod_cast hrpos
      nlinarith [hnqrR, hnmR, hrposR]
    have hpNat : m + 1 <= p := Nat.succ_le_of_lt hmp
    have hpReal : (m : Real) + 1 <= (p : Real) := by exact_mod_cast hpNat
    have hpupperN : p < n := by
      have hpLt : (p : Real) < (n : Real) := hpupper.trans_lt (by
        dsimp [x]
        have hdelta : (0 : Real) < 1 / (2 * 28314000) := by norm_num
        linarith)
      exact_mod_cast hpLt
    have hpupperReal : (p : Real) < (n : Real) := by exact_mod_cast hpupperN
    refine ⟨p, And.intro hp (And.intro ?_ hpupperReal)⟩
    linarith [htarget, hpReal]

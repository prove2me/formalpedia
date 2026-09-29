-- Prove2me | solution 1 for WeakGoldbach.prime_bracket_gap_lt_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:26:05.045716+00:00
-- url     : https://prove2.me/submissions/e4d3fd28-c571-47dd-9b87-ec572bceb88e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_RamareSaouter2003_prime_interval_large_range
import Theorems.Thm_WeakGoldbach_prime_bracket_gap_lt_4e18_upper_range

theorem solution (x : Nat)
    (hxl : Nat.le (10 ^ 26) x)
    (hx : Nat.le x (8875694145621773516800000000000 - 4 * 10 ^ 18)) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.le p x)
        (And (Nat.lt x q) (Nat.lt (Nat.sub q p) (4 * 10 ^ 18))))) := by
  by_cases hlow : x ≤ 105000000000000000000000000
  · have hxReal : (10 ^ (20 : Nat) : Real) ≤ (x : Real) := by
      have h : 10 ^ (20 : Nat) ≤ x := le_trans (by norm_num) hxl
      exact_mod_cast h
    have hxRealUpper : (x : Real) ≤ 105000000000000000000000000 := by
      exact_mod_cast hlow
    have hratioX : (x : Real) / 81353847 ≤ 1300000000000000000 := by
      calc
        (x : Real) / 81353847 ≤
            (105000000000000000000000000 : Real) / 81353847 := by
          exact div_le_div_of_nonneg_right hxRealUpper (by norm_num)
        _ ≤ 1300000000000000000 := by norm_num
    let y : Real := (x : Real) + 2700000000000000000
    have hyLower : (10 ^ (20 : Nat) : Real) ≤ y := by
      dsimp [y]
      have hxLower' : (10 ^ (20 : Nat) : Real) ≤ (x : Real) := hxReal
      linarith
    have hyUpper : y / 81353847 ≤ 1400000000000000000 := by
      have hyBound : y ≤ 107700000000000000000000000 := by
        dsimp [y]
        linarith
      calc
        y / 81353847 ≤
            (107700000000000000000000000 : Real) / 81353847 := by
          exact div_le_div_of_nonneg_right hyBound (by norm_num)
        _ ≤ 1400000000000000000 := by norm_num
    obtain ⟨p, hp, hpLower, hpUpper⟩ :=
      RamareSaouter2003.prime_interval_large_range (x : Real) hxReal
    obtain ⟨q, hq, hqLower, hqUpper⟩ :=
      RamareSaouter2003.prime_interval_large_range y hyLower
    have hpLower' : (x : Real) - 1300000000000000000 < (p : Real) := by
      have h := hpLower
      rw [show (x : Real) * (1 - 1 / 81353847) =
          (x : Real) - (x : Real) / 81353847 by ring] at h
      linarith
    have hqLower' : (x : Real) + 1300000000000000000 < (q : Real) := by
      have h := hqLower
      rw [show y * (1 - 1 / 81353847) = y - y / 81353847 by ring] at h
      dsimp [y] at h
      linarith
    have hpx : p ≤ x := by exact_mod_cast hpUpper
    have hpLowerCast : (x : Real) < (p : Real) + 1300000000000000000 := by
      linarith
    have hpLowerNat : x < p + 1300000000000000000 := by
      exact_mod_cast hpLowerCast
    have hxqStrong : x + 1300000000000000000 < q := by
      exact_mod_cast hqLower'
    have hxq : x < q := by omega
    have hqUpper' : q ≤ x + 2700000000000000000 := by
      have h : (q : Real) ≤ (x : Real) + 2700000000000000000 := by
        dsimp [y] at hqUpper
        exact hqUpper
      exact_mod_cast h
    have hq_lt_p : q < p + 4 * 10 ^ 18 := by
      norm_num at *
      omega
    have hpq : p ≤ q := le_trans hpx (Nat.le_of_lt hxq)
    have hgap : Nat.sub q p < 4 * 10 ^ 18 := by
      exact (Nat.sub_lt_iff_lt_add' hpq).2 hq_lt_p
    exact ⟨p, q, hp, hq, hpx, hxq, hgap⟩
  · have hhigh : 105000000000000000000000001 ≤ x := by omega
    exact WeakGoldbach.prime_bracket_gap_lt_4e18_upper_range x hhigh hx

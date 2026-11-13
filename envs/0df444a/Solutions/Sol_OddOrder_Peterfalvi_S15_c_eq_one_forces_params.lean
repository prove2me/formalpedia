-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.c_eq_one_forces_params
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:56:42.133535+00:00
-- url     : https://prove2.me/submissions/755fe9d5-2e8c-4198-94ea-573b50b27eae

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **Numerical core shared by Peterfalvi (13.12) and (13.15)**: the upper estimate
`m < q·p / ((2q+1)(p-1))` — obtained from `c ≥ 2q+1` (13.12) resp. the divisor `x ≥ 2q+1`
(13.15) together with the analytic inequality (13.10) and `u ≤ (p^q-1)/(p-1)` (13.2.c) — combined
with the (13.11) lower bounds on `m` forces `q = 3`.

Self-contained `ℚ`-arithmetic over an abstract `m` satisfying the (13.11.a,b) lower bounds; `p`, `q`
are odd primes so `p = 3 ∨ p ≥ 5` and `q = 3 ∨ q ≥ 5`, as supplied by the callers.

* `p ≥ 5`: `m < q·p/((2q+1)(p-1)) < (1/2)(5/4) = 5/8 < 7/10`, against `m > 7/10` (13.11.b).
* `p = 3`, `q ≥ 7`: `m < 3q/(2(2q+1)) < 3/4 < 8/10`, against `m > 8/10` (13.11.a).
* `p = 3`, `5 ≤ q < 7`: `m < 3q/(2(2q+1)) < 7/10`, against `m > 7/10` (13.11.b). -/
theorem caseB_numeric_forces_q_three {p q : ℕ} {m : ℚ}
    (hp : p = 3 ∨ 5 ≤ p) (hq : q = 3 ∨ 5 ≤ q)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hbound : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1))) :
    q = 3 := by
  rcases hq with hq3 | hq5
  · exact hq3
  exfalso
  have hqR : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq5
  have hm7over : (7 : ℚ) / 10 < m := hm5 hq5
  rcases hp with rfl | hp5
  · -- `p = 3`
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * (((3 : ℕ) : ℚ) - 1) := by
      rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num]; nlinarith [hqR]
    have hb := (lt_div_iff₀ hden).mp hbound
    rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num] at hb
    by_cases hq7 : 7 ≤ q
    · have h87 : (8 : ℚ) / 10 < m := hm7 hq7
      nlinarith [hb, h87, hqR]
    · have hqlt7 : (q : ℚ) < 7 := by exact_mod_cast (show q < 7 by omega)
      nlinarith [hb, hm7over, hqR, hqlt7]
  · -- `p ≥ 5`
    have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by nlinarith [hqR, hpR5]
    have hb := (lt_div_iff₀ hden).mp hbound
    nlinarith [hb, hm7over, hqR, hpR5]

/-- **Peterfalvi (13.12), numeric elimination** (04.15 p.85): the (13.10)+(13.2.c) upper bound
`m < q(p^q − 1)/(c · p^(q−1) · (p − 1))`, together with the fixed-point-free lower bound `c ≥ 2q+1`
(with `2q ∣ c − 1`) and the (13.11) lower bounds on `m`, forces `p = 5`, `q = 3`, `c = 7`.

This is the `sorry`-free `ℕ/ℚ`-arithmetic heart of (13.12): `q = 3` via
`caseB_numeric_forces_q_three`; the `q = 3` bound `m < 3(p³−1)/(c p²(p−1))` then eliminates `c ≥ 13`
(`< 49/100`, against (13.11.c)) forcing `c = 7`, eliminates `p ≥ 11` (`< 399/847 < 49/100`) forcing
`p < 11`, and eliminates `p = 7` (the exact value `m = ½ − 1/(2·3^{p−1}) = ½ − 1/1458` exceeds the
bound `171/343`) forcing `p = 5`.  Only the final `p = 5, q = 3, c = 7` structural contradiction
(`PC` normal nilpotent Hall ⊋ `P = S_F`) remains, isolated in `c_eq_one_final_case`. -/
theorem _root_.solution {p q c : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hc2q1 : 2 * q + 1 ≤ c) (h2q : 2 * q ∣ c - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hm49 : q = 3 → 5 ≤ p → (49 : ℚ) / 100 < m)
    (hmval : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hbound : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))) :
    p = 5 ∧ q = 3 ∧ c = 7 := by
  -- Basic positivity.
  have hpR : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hq3le : 3 ≤ q := by
    rcases hq.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hq2
  have hqR : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3le
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hcpos : 0 < c := by omega
  have hcR : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hcpos
  have hc2q1R : (2 * (q : ℚ) + 1) ≤ (c : ℚ) := by
    have : ((2 * q + 1 : ℕ) : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc2q1
    push_cast at this; linarith
  -- Odd prime `≥ 3` is `3` or `≥ 5`.
  have prime_split : ∀ n : ℕ, n.Prime → 3 ≤ n → n = 3 ∨ 5 ≤ n := by
    intro n hn hn3
    by_contra hcon
    rw [not_or, not_le] at hcon
    obtain ⟨hne, hlt⟩ := hcon
    interval_cases n
    · exact hne rfl
    · exact (by norm_num : ¬ Nat.Prime 4) hn
  have hp35 : p = 3 ∨ 5 ≤ p := prime_split p hp hp3
  have hq35 : q = 3 ∨ 5 ≤ q := prime_split q hq hq3le
  -- `p^q = p^(q-1) · p`.
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  -- Step 1: derive `m < q p / ((2q+1)(p-1))`, hence `q = 3`.
  have hbound2q1 : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
    have hden1 : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1) := by positivity
    have hden2 : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by positivity
    have hstep : (q : ℚ) * ((p : ℚ) ^ q - 1) / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))
        < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
      rw [div_lt_div_iff₀ hden1 hden2, hpexp]
      have hkey : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
          < (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by
        have hpp : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (p : ℚ) := by positivity
        have e1 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
            < (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by nlinarith [hqR, hpp]
        have e2 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ))
            ≤ (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) :=
          mul_le_mul_of_nonneg_right hc2q1R (le_of_lt hpp)
        linarith [e1, e2]
      have hqp1 : (0 : ℚ) < (q : ℚ) * ((p : ℚ) - 1) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hkey hqp1]
    linarith [hbound, hstep]
  have hq3 : q = 3 := caseB_numeric_forces_q_three hp35 hq35 hm5 hm7 hbound2q1
  -- With `q = 3`, `p ≥ 5`.
  have hp5 : 5 ≤ p := by
    rcases hp35 with h | h
    · exact absurd (h.trans hq3.symm) hpq
    · exact h
  have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
  subst hq3
  -- Specialize the bound to `q = 3`.
  have hbound3 : m < (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1)) := by
    have he : (p : ℚ) ^ (3 - 1) = (p : ℚ) ^ 2 := by norm_num
    have hc3 : ((3 : ℕ) : ℚ) = (3 : ℚ) := by norm_num
    rw [he, hc3] at hbound
    exact hbound
  have hm49p : (49 : ℚ) / 100 < m := hm49 rfl hp5
  -- `c ≡ 1 mod 6`, `c ≥ 7`, so `c = 7 ∨ c ≥ 13`.
  have h6 : 6 ∣ c - 1 := by simpa using h2q
  have hc7or13 : c = 7 ∨ 13 ≤ c := by omega
  -- Kill `c ≥ 13`.
  have hc7 : c = 7 := by
    rcases hc7or13 with h | h
    · exact h
    exfalso
    have hcR13 : (13 : ℚ) ≤ (c : ℚ) := by exact_mod_cast h
    have hden : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb13 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hcR13, hpR5, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1,
        sq_nonneg ((p : ℚ) - 5)]
    linarith [hbound3, hb13, hm49p]
  subst hc7
  -- Kill `p ≥ 11`.
  have hp_lt_11 : p < 11 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpR11 : (11 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hcon
    have hden : (0 : ℚ) < (7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb11 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hpR11, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1]
    linarith [hbound3, hb11, hm49p]
  -- Kill `p = 7` via the exact value of `m`.
  have hp_ne_7 : p ≠ 7 := by
    intro h7
    subst h7
    rw [hmval] at hbound3
    norm_num at hbound3
  -- `5 ≤ p < 11`, prime, `≠ 7` ⇒ `p = 5`.
  refine ⟨?_, rfl, rfl⟩
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exact absurd rfl hp_ne_7
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

end OddOrder.Peterfalvi.S15

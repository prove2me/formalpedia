-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.caseB_order_x_absurd_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:55:59.608701+00:00
-- url     : https://prove2.me/submissions/316e2574-4d3d-4969-bb24-a2352087da22

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CaseBOrder.lean
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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CaseBOrder.lean =====
namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

/-- `(p³ − 1)/(p − 1) = p² + p + 1` over `ℕ` (the geometric-sum identity for `q = 3`). -/
theorem cyclotomic_quotient_three {p : ℕ} (hp : 2 ≤ p) :
    (p ^ 3 - 1) / (p - 1) = p ^ 2 + p + 1 := by
  rw [← Nat.geomSum_eq hp 3, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  ring

/-- **Peterfalvi (13.15), the `x ≥ 2q + 1` elimination** (side-agnostic numeric engine).

If the cofactor `x` (with `u·x = (p^q − 1)/(p − 1)`) satisfies `x ≥ 2q + 1`, the analytic inequality
`hanalytic` (from (13.10)+(13.12): `m < q(p^q − 1) / (p^{q−1} · x · (p − 1))`) together with the
(13.11) lower bounds on `m` and the (13.11.c) bound `(p² − 1)/6 < u` are contradictory.

Mirrors `c_eq_one_forces_params`: the `q = 3` reduction (via `caseB_numeric_forces_q_three`) and the
`m < qp/((2q+1)(p−1))` step are identical (with `x` in place of `c`); the endgame differs — here
`p² − 6p − 13 < 0` forces `p ∈ {5, 7}`, and `x ∣ (p² + p + 1) ∈ {31, 57}` with `x ≥ 7`, `u ≠ 1`,
`q ∤ u` is impossible.  All char/`σ`-theory content is supplied by the caller as the hypotheses
`hanalytic`, `hm5`, `hm7`, `h11c`, `hu_cop_q` (⟵ (13.14)). -/
theorem _root_.solution {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hx : 2 * q + 1 ≤ x)
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    False := by
  -- Positivity / prime facts (mirroring `c_eq_one_forces_params`).
  have hpR : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hq3le : 3 ≤ q := by
    rcases hq.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hq2
  have hqR : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3le
  have hq0 : (0 : ℚ) < (q : ℚ) := by linarith
  have hx2q1R : (2 * (q : ℚ) + 1) ≤ (x : ℚ) := by
    have h : ((2 * q + 1 : ℕ) : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
    push_cast at h; linarith
  have hxR : (0 : ℚ) < (x : ℚ) := by linarith
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
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  -- Step 1: `m < qp/((2q+1)(p-1))`, hence `q = 3` (identical to `c_eq_one_forces_params`, `x` for
  -- `c`).
  have hbound2q1 : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
    have hden1 : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1) := by positivity
    have hden2 : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by positivity
    have hstep : (q : ℚ) * ((p : ℚ) ^ q - 1) / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))
        < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
      rw [div_lt_div_iff₀ hden1 hden2, hpexp]
      have hpp : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (p : ℚ) := by positivity
      have hkey : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
          < (x : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by
        have e1 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
            < (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by nlinarith [hqR, hpp]
        have e2 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ))
            ≤ (x : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) :=
          mul_le_mul_of_nonneg_right hx2q1R (le_of_lt hpp)
        linarith [e1, e2]
      have hqp1 : (0 : ℚ) < (q : ℚ) * ((p : ℚ) - 1) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hkey hqp1]
    linarith [hanalytic, hstep]
  have hq3 : q = 3 := caseB_numeric_forces_q_three hp35 hq35 hm5 hm7 hbound2q1
  have hp5 : 5 ≤ p := by
    rcases hp35 with h | h
    · exact absurd (h.trans hq3.symm) hpq
    · exact h
  subst hq3
  -- `q = 3`: `u·x = p² + p + 1`, `x ≥ 7`, so `x ∣ p² + p + 1` and `7u ≤ p² + p + 1`.
  have hval : (p ^ 3 - 1) / (p - 1) = p ^ 2 + p + 1 := cyclotomic_quotient_three hp.two_le
  rw [hval] at hux
  have hx7 : 7 ≤ x := by omega
  have hu_le7 : 7 * u ≤ p ^ 2 + p + 1 := by
    have h : 7 * u ≤ x * u := by gcongr
    rw [mul_comm x u, hux] at h
    exact h
  -- (13.11.c): `(p² − 1)/6 < u`; with `7u ≤ p² + p + 1` this forces `p ∈ {5, 7}`.
  have hu_le7R : (7 : ℚ) * (u : ℚ) ≤ (p : ℚ) ^ 2 + (p : ℚ) + 1 := by
    have h : ((7 * u : ℕ) : ℚ) ≤ ((p ^ 2 + p + 1 : ℕ) : ℚ) := by exact_mod_cast hu_le7
    push_cast at h; linarith
  have hp_lt_8 : p < 8 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpR8 : (8 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hcon
    have h6u : (p : ℚ) ^ 2 - 1 < 6 * (u : ℚ) := by
      have h := h11c rfl
      rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 6)] at h
      linarith
    have hprod : (0 : ℚ) ≤ ((p : ℚ) - 8) * ((p : ℚ) + 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h6u, hu_le7R, hprod]
  -- `5 ≤ p < 8`, prime ⟹ `p = 5 ∨ p = 7`, and each is impossible.
  interval_cases p
  · -- `p = 5`: `u·x = 31` (prime), `7u ≤ 31 ⟹ u ≤ 4`, `u ∣ 31` ⟹ `u = 1`, contra `hu_ne_one`.
    norm_num at hux hu_le7
    have hu4 : u ≤ 4 := by omega
    interval_cases u <;> omega
  · exact absurd hp (by norm_num)
  · -- `p = 7`: `u·x = 57 = 3·19`, `7u ≤ 57 ⟹ u ≤ 8`; `u ∈ {1, 3}` excluded (`hu_ne_one`, `q ∤ u`).
    norm_num at hux hu_le7
    have hu8 : u ≤ 8 := by omega
    interval_cases u <;> omega

end OddOrder.Peterfalvi.S15

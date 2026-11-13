-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.numeric_bounds_of_analytic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:57:46.473693+00:00
-- url     : https://prove2.me/submissions/5613ef2c-66d4-4841-a670-0c8f8e2ce883

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

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11)** numeric core of the `q = 3` branch: once the
Section 16 hypothesis gives `p ≥ 5`, the concrete value of `m` is already
strictly larger than `49/100`. -/
theorem m_value_q_three_gt_49_hundredths {p : ℕ} (hp : 5 ≤ p) :
    (49 : ℚ) / 100 <
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
        1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p) := by
  have h4 : 4 ≤ p - 1 := by omega
  have hpow4 : (3 : ℚ) ^ 4 ≤ (3 : ℚ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 3) h4
  norm_num at hpow4
  have hden_gt : (100 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hsmall : 1 / (2 * (3 : ℚ) ^ (p - 1)) < (1 : ℚ) / 100 := by
    rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 100)]
    nlinarith
  have hpow : (3 : ℚ) ^ p = 3 * (3 : ℚ) ^ (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by omega
    rw [hp_eq, pow_succ]
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    ring
  have hexpr :
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
          1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p)
        = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (p - 1)) := by
    rw [hpow]
    field_simp [hden_pos.ne']
    ring
  rw [hexpr]
  linarith [hsmall]

/-- Exponential estimate used in **Peterfalvi (13.11.c)**: for `n ≥ 5`,
`n² ≤ 3^(n-1)`.  The induction step is `(n+1)² ≤ 3n²`. -/
private theorem sq_le_three_pow_pred_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    n ^ 2 ≤ 3 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
      calc
        (n + 1) ^ 2 ≤ 3 * n ^ 2 := hstep
        _ ≤ 3 * 3 ^ (n - 1) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (n + 1 - 1) := by
          rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
          ring

namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

/-- **Peterfalvi (13.11)** at the Section 15 hypothesis level: in the `q = 3`
branch, the `m > 49/100` part follows once an external argument supplies
`p ≥ 5`.  Section 16 supplies this from `q < p`. -/
theorem m_gt_49_hundredths_of_q_eq_three_of_five_le_p
    (hyp : Hypothesis (G := G)) (hq3 : hyp.q = 3) (hp5 : 5 ≤ hyp.p) :
    hyp.m > (49 / 100 : ℚ) := by
  rw [hyp.m_eq, hq3]
  exact m_value_q_three_gt_49_hundredths hp5

end Hypothesis

/-- **Peterfalvi (13.11)**: the elementary numerical bounds for `m`.

The `q ≥ 7` and `q ≥ 5` bounds are the genuine arithmetic estimates
`m_value_gt_four_fifths` / `m_value_gt_seven_tenths` applied through the now
concrete value `m_eq` (they need only `p ≥ 3`, supplied by `three_le_p`).  The
`q = 3` branch uses `p ≠ q` and oddness to get `p ≥ 5`; its `m`-bound is
`m_value_q_three_gt_49_hundredths`, while the `u/c` bound combines the analytic
inequality (13.10) with `p² ≤ 3^(p-1)`. -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by
  refine ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q, fun hq3 => ?_⟩
  have hp5 : 5 ≤ hyp.p := by
    have hp3 := hyp.three_le_p
    have hpne3 : hyp.p ≠ 3 := by
      intro hp3eq
      exact hyp.p_ne_q (hp3eq.trans hq3.symm)
    obtain ⟨k, hk⟩ := hyp.p_odd
    omega
  have hm49 := hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hp5
  rw [hq3] at h1310
  norm_num at h1310
  have hpPow : hyp.p ^ 2 ≤ 3 ^ (hyp.p - 1) :=
    sq_le_three_pow_pred_of_five_le hp5
  have hpPowR : (hyp.p : ℚ) ^ 2 ≤ (3 : ℚ) ^ (hyp.p - 1) := by
    exact_mod_cast hpPow
  have hmval := hyp.m_eq
  rw [hq3] at hmval
  norm_num at hmval
  have hmval' : hyp.m = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (hyp.p - 1)) := by
    rw [hmval]
    have hpow : (3 : ℚ) ^ hyp.p = 3 * (3 : ℚ) ^ (hyp.p - 1) := by
      conv_lhs => rw [show hyp.p = (hyp.p - 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    field_simp
    ring
  have hden : (0 : ℚ) < (3 : ℚ) ^ (hyp.p - 1) := by positivity
  have hfrac : (hyp.p : ℚ) ^ 2 / (3 : ℚ) ^ (hyp.p - 1) ≤ 1 := by
    rw [div_le_one hden]
    exact hpPowR
  have hlower : (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6) ≤
      hyp.m * (((hyp.p ^ 2 : ℕ) : ℚ)) / 3 := by
    have hp2pos : 1 ≤ hyp.p ^ 2 := Nat.one_le_pow _ _ hyp.p_prime.pos
    rw [hmval']
    push_cast [Nat.cast_sub hp2pos]
    have hid : ((1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (hyp.p - 1))) *
          (hyp.p : ℚ) ^ 2 / 3 =
        ((hyp.p : ℚ) ^ 2 - (hyp.p : ℚ) ^ 2 / (3 : ℚ) ^ (hyp.p - 1)) / 6 := by
      field_simp [hden.ne']
      ring
    rw [hid]
    linarith [hfrac]
  exact ⟨hm49, lt_of_le_of_lt hlower h1310⟩

end OddOrder.Peterfalvi.S15

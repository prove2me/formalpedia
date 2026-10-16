-- Prove2me | solution 1 for SwitchbackExp.Design.lemma_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:30:15.042531+00:00
-- url     : https://prove2.me/submissions/7d202c86-aa68-4cff-b697-837c681be6f1

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

set_option autoImplicit false
open scoped BigOperators

namespace SwitchbackResearch

theorem reciprocal_pair (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : a * b ≤ 1) :
    2 ≤ 1 / a + 1 / b ∧ (1 / a + 1 / b = 2 → a * b = 1) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hid : 1 / a + 1 / b = (a + b) / (a * b) := by field_simp; ring
  rw [hid]
  constructor
  · apply (le_div_iff₀ hab).2
    have hh := mul_nonneg hab.le (sub_nonneg.mpr hp)
    nlinarith [sq_nonneg (a - b)]
  · intro he
    have he' := (div_eq_iff (ne_of_gt hab)).mp he
    apply le_antisymm hp
    by_contra hn
    have hlt : a * b < 1 := lt_of_not_ge hn
    have hh := mul_pos hab (sub_pos.mpr hlt)
    nlinarith [sq_nonneg (a - b)]

end SwitchbackResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Bojinov, Simchi-Levi and Zhao, arXiv:2009.00148v4, Lemma EC.2.
theorem solution (n : ℕ) (q : Fin n → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) :
    2 ^ (n + 1) ≤ 1 / ∏ i, q i + 1 / ∏ i, (1 - q i) ∧
    (1 / ∏ i, q i + 1 / ∏ i, (1 - q i) = 2 ^ (n + 1) ↔ ∀ i, q i = 1 / 2) := by
  classical
  let A := ∏ i, q i
  let B := ∏ i, (1 - q i)
  let t : ℝ := 2 ^ n
  have hA : 0 < A := Finset.prod_pos (fun i _ => (hq i).1)
  have hB : 0 < B := Finset.prod_pos (fun i _ => sub_pos.mpr (hq i).2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hfac (i : Fin n) : 0 < 4 * q i * (1 - q i) ∧ 4 * q i * (1 - q i) ≤ 1 := by
    constructor
    · exact mul_pos (mul_pos (by norm_num) (hq i).1) (sub_pos.mpr (hq i).2)
    · nlinarith [sq_nonneg (2 * q i - 1)]
  have hprod : (∏ i, 4 * q i * (1 - q i)) = (t * A) * (t * B) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change (4 : ℝ)^n * A * B = (t * A) * (t * B)
    have hp : (4 : ℝ)^n = t * t := by
      dsimp [t]
      calc
        (4 : ℝ)^n = (2 * 2 : ℝ)^n := by norm_num
        _ = 2^n * 2^n := mul_pow _ _ _
    rw [hp]
    ring
  have hp : (t * A) * (t * B) ≤ 1 := by
    rw [← hprod]
    exact Finset.prod_le_one (fun i _ => (hfac i).1.le) (fun i _ => (hfac i).2)
  have hb := SwitchbackResearch.reciprocal_pair (t * A) (t * B)
    (mul_pos ht hA) (mul_pos ht hB) hp
  have hid : t * (1 / (t * A) + 1 / (t * B)) = 1 / A + 1 / B := by
    field_simp
  have hpow : (2 : ℝ)^(n + 1) = 2 * t := by dsimp [t]; rw [pow_succ]; ring
  constructor
  · change 2^(n + 1) ≤ 1 / A + 1 / B
    rw [hpow, ← hid]
    simpa only [mul_comm t 2] using mul_le_mul_of_nonneg_left hb.1 ht.le
  · constructor
    · intro he
      change 1 / A + 1 / B = 2^(n + 1) at he
      rw [hpow, ← hid] at he
      have he' : 1 / (t * A) + 1 / (t * B) = 2 := by nlinarith
      have hpeq : (∏ i, 4 * q i * (1 - q i)) = 1 := hprod.trans (hb.2 he')
      intro i
      by_contra hn
      have hfi : 4 * q i * (1 - q i) < 1 := by
        have hne : 2 * q i - 1 ≠ 0 := by intro h; apply hn; linarith
        have hs := sq_pos_of_ne_zero hne
        nlinarith
      have hlt : (∏ j, 4 * q j * (1 - q j)) < ∏ _j : Fin n, (1 : ℝ) :=
        Finset.prod_lt_prod (fun j _ => (hfac j).1) (fun j _ => (hfac j).2)
          ⟨i, Finset.mem_univ i, hfi⟩
      simp only [Finset.prod_const_one, hpeq] at hlt
      exact lt_irrefl _ hlt
    · intro he
      simp only [he]
      norm_num [Finset.prod_const, pow_succ, div_pow]
      ring

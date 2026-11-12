-- Prove2me | solution 1 for PGDMap20261031.step_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T15:32:19.826541+00:00
-- url     : https://prove2.me/submissions/ebd55094-f3ec-4100-864b-70c69ee49aa6

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Stepsize
import Theorems.Thm_PGDMap20261031_step_balance

open PGDMap20261031
noncomputable section
open scoped BigOperators

private lemma even_power (h : ℝ) (k : ℕ) : (1 - h) ^ (2 * k) = (h - 1) ^ (2 * k) := by
  rw [pow_mul, pow_mul]
  congr 1
  ring

private lemma denominatorA_pos (N : ℕ) (h q : ℝ) (hN : 1 ≤ N)
    (hh : validStep h) (hq : 0 < q) : 0 < (base h q) ^ (2 * N) - 1 - h ^ 2 * q := by
  have hb : 1 ≤ base h q := by unfold base; nlinarith [hh.1]
  have hpow : (base h q) ^ 2 ≤ (base h q) ^ (2 * N) :=
    pow_le_pow_right₀ hb (by omega)
  have hinner : 0 < 2 - h + h * q := by nlinarith [hh.1, hh.2]
  have hprod := mul_pos (mul_pos hh.1 hq) hinner
  dsimp [base] at hpow ⊢
  nlinarith only [hpow, hprod]

private lemma denominatorB_pos (N : ℕ) (h q : ℝ) (hN : 1 ≤ N)
    (hh : validStep h) (hq : 0 ≤ q) : 0 < (base h q) ^ (2 * N) - (1 - h) ^ (2 * N) := by
  have hb : 1 ≤ base h q := by unfold base; nlinarith [hh.1]
  have habs : |1 - h| < 1 := abs_lt.mpr ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have hp : |1 - h| ^ (2 * N) < 1 := pow_lt_one₀ (abs_nonneg _) habs (by omega)
  have hp' : (1 - h) ^ (2 * N) < 1 := lt_of_le_of_lt (le_abs_self _) (by simpa [abs_pow] using hp)
  linarith [one_le_pow₀ hb (n := 2 * N)]

private def crossingPolynomial (N : ℕ) (q h : ℝ) : ℝ :=
  if q = 0 then (h - 1) ^ (2 * (N - 1)) * (1 + 2 * ((N - 1 : ℕ) : ℝ) * h) - 1
  else (h - 1) ^ (2 * (N - 1)) * ((1 + q) * (base h q) ^ (2 * (N - 1)) - 1) -
    q * (base h q) ^ (2 * (N - 1))

private lemma crossing_iff (N : ℕ) (q h : ℝ) (hN : 2 ≤ N)
    (hq : 0 ≤ q) (hh : h ∈ Set.Ioo (1 : ℝ) 2) :
    branchA N h q = branchB N h q ↔ crossingPolynomial N q h = 0 := by
  let k := N - 1
  have hm : 2 * N = 2 * k + 2 := by dsimp [k]; omega
  have hm2 : 2 * N - 2 = 2 * k := by dsimp [k]; omega
  have hNr : (N : ℝ) = (k : ℝ) + 1 := by exact_mod_cast (show N = k + 1 by dsimp [k]; omega)
  have hNrlo : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hv : validStep h := ⟨by linarith [hh.1], hh.2⟩
  have hdb := denominatorB_pos N h q (by omega) hv hq
  by_cases hz : q = 0
  · subst q
    have hda : 0 < h * (2 * (N : ℝ) - h) := mul_pos hv.1 (by linarith [hh.2])
    simp only [base, mul_zero, add_zero, one_pow] at hdb
    rw [even_power h N] at hdb
    simp only [hm, pow_add, pow_two] at hdb
    simp only [branchA, branchB]
    simp only [base, mul_zero, add_zero, one_pow, mul_one]
    simp only [ite_true]
    rw [hm2, even_power h k, even_power h N]
    simp only [hm, pow_add, pow_two]
    rw [div_eq_div_iff hda.ne' hdb.ne']
    unfold crossingPolynomial
    rw [if_pos (rfl : (0 : ℝ) = 0)]
    change _ ↔ (h - 1) ^ (2 * k) * (1 + 2 * (k : ℝ) * h) - 1 = 0
    have hid : 2 * (1 - (h - 1) ^ (2 * k) * ((h - 1) * (h - 1))) -
        (2 * (h - 1) ^ (2 * k)) * (h * (2 * (N : ℝ) - h)) =
        -2 * ((h - 1) ^ (2 * k) * (1 + 2 * (k : ℝ) * h) - 1) := by
      rw [hNr]
      ring
    constructor <;> intro heq <;> linarith only [hid, heq]
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    have hda := denominatorA_pos N h q (by omega) hv hqp
    simp only [branchA, branchB, if_neg hz]
    rw [hm2, even_power h k, even_power h N]
    rw [even_power h N] at hdb
    simp only [hm, pow_add, pow_two] at hda hdb ⊢
    rw [div_eq_div_iff hda.ne' hdb.ne']
    unfold crossingPolynomial
    rw [if_neg hz]
    change _ ↔ (h - 1) ^ (2 * k) * ((1 + q) * (base h q) ^ (2 * k) - 1) -
      q * (base h q) ^ (2 * k) = 0
    let P := (h - 1) ^ (2 * k) * ((1 + q) * (base h q) ^ (2 * k) - 1) -
      q * (base h q) ^ (2 * k)
    have hid : 2 * q * ((base h q) ^ (2 * k) * (base h q * base h q) -
        (h - 1) ^ (2 * k) * ((h - 1) * (h - 1))) -
        (2 * (1 + q) * (h - 1) ^ (2 * k)) *
          ((base h q) ^ (2 * k) * (base h q * base h q) - 1 - h * h * q) =
        (-2 * (base h q) ^ 2) * P := by
      dsimp [P, base]
      ring
    have hfactor : -2 * (base h q) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (by unfold base; nlinarith [hv.1]))
    constructor
    · intro heq
      exact (mul_eq_zero.mp (show (-2 * (base h q) ^ 2) * P = 0 by
        linarith only [hid, heq])).resolve_left hfactor
    · intro heq
      have hP : P = 0 := heq
      rw [hP, mul_zero] at hid
      linarith only [hid]

private lemma polynomial_continuous (N : ℕ) (q : ℝ) : Continuous (crossingPolynomial N q) := by
  unfold crossingPolynomial
  split_ifs <;> (try dsimp only [base]) <;> fun_prop

private lemma polynomial_right_pos (N : ℕ) (q : ℝ) (hN : 2 ≤ N) (hq : 0 ≤ q) :
    0 < crossingPolynomial N q 2 := by
  have hk : (1 : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast (show 1 ≤ N - 1 by omega)
  have hn : 2 * (N - 1) ≠ 0 := by omega
  by_cases hz : q = 0
  · simp only [crossingPolynomial, if_pos hz]
    norm_num
    linarith
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    have hp : 1 < (1 + 2 * q) ^ (2 * (N - 1)) := by
      simpa using pow_lt_pow_left₀ (by linarith : (1 : ℝ) < 1 + 2 * q)
        (by norm_num : (0 : ℝ) ≤ 1) hn
    have heq : crossingPolynomial N q 2 = (1 + 2 * q) ^ (2 * (N - 1)) - 1 := by
      simp only [crossingPolynomial, if_neg hz, base]
      norm_num
      ring
    rw [heq]
    linarith only [hp]

private lemma below_optimum (N : ℕ) (q h : ℝ) (hN : 2 ≤ N) (hq : 0 ≤ q)
    (hh : h ∈ Set.Ioo (1 : ℝ) 2) (hneg : crossingPolynomial N q h < 0) :
    h < optimalStep N q := by
  have hright := polynomial_right_pos N q hN hq
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc hh.2.le
    (polynomial_continuous N q).continuousOn
    (show (0 : ℝ) ∈ Set.Icc (crossingPolynomial N q h) (crossingPolynomial N q 2)
      from ⟨hneg.le, hright.le⟩)
  have hhu : h < u := by
    apply lt_of_le_of_ne hu.1
    intro heq
    rw [heq, hzero] at hneg
    exact lt_irrefl _ hneg
  have hu2 : u < 2 := by
    apply lt_of_le_of_ne hu.2
    intro heq
    rw [← heq, hzero] at hright
    exact lt_irrefl _ hright
  have hu1 : 1 < u := lt_trans hh.1 hhu
  have hbalance := PGDMap20261031.step_balance N q hN hq
  have heq := hbalance.2.2.2.2 u hu1 hu2 ((crossing_iff N q u hN hq ⟨hu1, hu2⟩).mpr hzero)
  simpa only [heq] using hhu

private lemma after_return_decreases (F : ℕ → ℝ) (u : ℝ) (hu : 0 < u)
    (hanti : StrictAnti (fun n => (F (n + 1) - F n) / u ^ n))
    (k l : ℕ) (hk : 0 < k) (hkl : k < l) (hreturn : F k = F 0) : F l < F k := by
  have hak : (F (k + 1) - F k) / u ^ k < 0 := by
    by_contra hn
    have haknonneg := le_of_not_gt hn
    have hjpos (j : ℕ) (hj : j ∈ Finset.range k) : 0 < F (j + 1) - F j := by
      have hlt := hanti (Finset.mem_range.mp hj)
      have hratio : 0 < (F (j + 1) - F j) / u ^ j := lt_of_le_of_lt haknonneg hlt
      exact (div_pos_iff_of_pos_right (pow_pos hu _)).mp hratio
    have hsum : 0 < ∑ j ∈ Finset.range k, (F (j + 1) - F j) := by
      apply Finset.sum_pos' (fun j hj => (hjpos j hj).le)
      exact ⟨0, Finset.mem_range.mpr hk, hjpos 0 (Finset.mem_range.mpr hk)⟩
    rw [Finset.sum_range_sub, hreturn, sub_self] at hsum
    exact lt_irrefl _ hsum
  have hstep (n : ℕ) (hn : k ≤ n) : F (n + 1) < F n := by
    have ha : (F (n + 1) - F n) / u ^ n < 0 :=
      lt_of_le_of_lt (hanti.antitone hn) hak
    have hdiff : F (n + 1) - F n < 0 := by
      have := (div_lt_iff₀ (pow_pos hu n)).mp ha
      simpa only [zero_mul] using this
    linarith only [hdiff]
  have hle (n : ℕ) (hn : k ≤ n) : F n ≤ F k := by
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact le_trans (hstep n hn).le ih
  have hlast := lt_of_lt_of_le (hstep (l - 1) (by omega)) (hle (l - 1) (by omega))
  simpa only [Nat.sub_add_cancel (show 1 ≤ l by omega)] using hlast

private lemma reciprocal_sum_identity (b : ℝ) (hb : b ≠ 0) (m : ℕ) :
    (b - 1) * (∑ j ∈ Finset.range m, (b⁻¹) ^ (j + 1)) = 1 - (b⁻¹) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hcancel := mul_inv_cancel₀ hb
    linear_combination ih + (b⁻¹) ^ m * hcancel

private def reciprocalSum (m : ℕ) (b : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (b⁻¹) ^ (j + 1)

private lemma polynomial_sum_identity (N : ℕ) (q h : ℝ) (_hN : 2 ≤ N)
    (hq : 0 < q) (hh : 1 < h) :
    crossingPolynomial N q h = q * (base h q) ^ (2 * (N - 1)) *
      ((h - 1) ^ (2 * (N - 1)) * (1 + h * reciprocalSum (2 * (N - 1)) (base h q)) - 1) := by
  let b := base h q
  let m := 2 * (N - 1)
  have hb : b ≠ 0 := by dsimp [b, base]; nlinarith
  have hbq : b = 1 + h * q := rfl
  have hsum := reciprocal_sum_identity b hb m
  have hpow : b ^ m * (b⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hb, one_pow]
  unfold crossingPolynomial
  rw [if_neg hq.ne']
  change (h - 1) ^ m * ((1 + q) * b ^ m - 1) - q * b ^ m =
    q * b ^ m * ((h - 1) ^ m * (1 + h * (∑ j ∈ Finset.range m, (b⁻¹) ^ (j + 1))) - 1)
  linear_combination (h - 1) ^ m * hpow - (h - 1) ^ m * b ^ m * hsum +
    (h - 1) ^ m * b ^ m * (∑ j ∈ Finset.range m, (b⁻¹) ^ (j + 1)) * hbq

private lemma normalized_root (N : ℕ) (q h : ℝ) (hN : 2 ≤ N) (hq : 0 ≤ q)
    (hh : h ∈ Set.Ioo (1 : ℝ) 2) (hroot : crossingPolynomial N q h = 0) :
    (h - 1) ^ (2 * (N - 1)) * (1 + h * reciprocalSum (2 * (N - 1)) (base h q)) = 1 := by
  by_cases hz : q = 0
  · subst q
    have hsum : reciprocalSum (2 * (N - 1)) (base h 0) = (2 * (N - 1) : ℕ) := by
      simp [reciprocalSum, base]
    rw [hsum]
    unfold crossingPolynomial at hroot
    rw [if_pos rfl] at hroot
    push_cast
    nlinarith only [hroot]
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    rw [polynomial_sum_identity N q h hN hqp hh.1] at hroot
    have hb : 0 < base h q := by unfold base; nlinarith [hh.1]
    have hfactor := mul_pos hqp (pow_pos hb (2 * (N - 1)))
    exact sub_eq_zero.mp ((mul_eq_zero.mp hroot).resolve_left hfactor.ne')

private lemma reciprocalSum_strictAnti (m : ℕ) (hm : 0 < m) (b₁ b₂ : ℝ)
    (hb₁ : 0 < b₁) (hbb : b₁ < b₂) : reciprocalSum m b₂ < reciprocalSum m b₁ := by
  have hb₂ : 0 < b₂ := lt_trans hb₁ hbb
  have hinv : b₂⁻¹ < b₁⁻¹ := (inv_lt_inv₀ hb₂ hb₁).mpr hbb
  have hterm (j : ℕ) : (b₂⁻¹) ^ (j + 1) < (b₁⁻¹) ^ (j + 1) :=
    pow_lt_pow_left₀ hinv (inv_pos.mpr hb₂).le (by omega)
  exact Finset.sum_lt_sum (fun j _ => (hterm j).le)
    ⟨0, Finset.mem_range.mpr hm, hterm 0⟩

private lemma optimum_q_strict (N : ℕ) (q₁ q₂ : ℝ) (hN : 2 ≤ N)
    (hq₁ : 0 ≤ q₁) (hq₁₂ : q₁ < q₂) : optimalStep N q₁ < optimalStep N q₂ := by
  let h := optimalStep N q₁
  have hbal := PGDMap20261031.step_balance N q₁ hN hq₁
  have hh : h ∈ Set.Ioo (1 : ℝ) 2 := ⟨hbal.1, hbal.2.1⟩
  have hroot := (crossing_iff N q₁ h hN hq₁ hh).mp hbal.2.2.2.1
  have hnormalized := normalized_root N q₁ h hN hq₁ hh hroot
  have hq₂ : 0 < q₂ := lt_of_le_of_lt hq₁ hq₁₂
  have hb₁ : 0 < base h q₁ := by unfold base; nlinarith [hh.1]
  have hbb : base h q₁ < base h q₂ := by
    unfold base
    nlinarith [mul_pos (by linarith [hh.1] : 0 < h) (sub_pos.mpr hq₁₂)]
  have hsum := reciprocalSum_strictAnti (2 * (N - 1)) (by omega)
    (base h q₁) (base h q₂) hb₁ hbb
  have hpow : 0 < (h - 1) ^ (2 * (N - 1)) := pow_pos (by linarith [hh.1]) _
  have hless : (h - 1) ^ (2 * (N - 1)) *
      (1 + h * reciprocalSum (2 * (N - 1)) (base h q₂)) < 1 := by
    have hprod := mul_pos hpow (mul_pos (by linarith [hh.1] : 0 < h) (sub_pos.mpr hsum))
    nlinarith only [hprod, hnormalized]
  apply below_optimum N q₂ h hN hq₂.le hh
  rw [polynomial_sum_identity N q₂ h hN hq₂ hh.1]
  exact mul_neg_of_pos_of_neg (mul_pos hq₂ (pow_pos (lt_trans hb₁ hbb) _)) (sub_neg.mpr hless)

private lemma optimum_N_strict (N₁ N₂ : ℕ) (q : ℝ) (hN₁ : 2 ≤ N₁)
    (hN₁₂ : N₁ < N₂) (hq : 0 ≤ q) : optimalStep N₁ q < optimalStep N₂ q := by
  let h := optimalStep N₁ q
  let t := h - 1
  let u := t ^ 2
  have hbal := PGDMap20261031.step_balance N₁ q hN₁ hq
  have hh : h ∈ Set.Ioo (1 : ℝ) 2 := ⟨hbal.1, hbal.2.1⟩
  have ht : 0 < t := by dsimp [t]; linarith [hh.1]
  have ht1 : t < 1 := by dsimp [t]; linarith [hh.2]
  have hu : 0 < u := pow_pos ht 2
  have hu1 : u < 1 := pow_lt_one₀ ht.le ht1 (by norm_num)
  have hroot := (crossing_iff N₁ q h hN₁ hq hh).mp hbal.2.2.2.1
  have huk (n : ℕ) : u ^ n = t ^ (2 * n) := by dsimp [u]; rw [← pow_mul]
  apply below_optimum N₂ q h (by omega) hq hh
  by_cases hz : q = 0
  · subst q
    let F : ℕ → ℝ := fun n => u ^ n * (1 + 2 * (n : ℝ) * h)
    have hnorm (n : ℕ) : (F (n + 1) - F n) / u ^ n =
        (u - 1) * (1 + 2 * (n : ℝ) * h) + 2 * h * u := by
      dsimp [F]
      push_cast
      rw [pow_succ]
      field_simp [(pow_pos hu n).ne']
      ring
    have hanti : StrictAnti (fun n => (F (n + 1) - F n) / u ^ n) := by
      intro i j hij
      change (F (j + 1) - F j) / u ^ j < (F (i + 1) - F i) / u ^ i
      rw [hnorm i, hnorm j]
      have hijr : (i : ℝ) < j := by exact_mod_cast hij
      have hprod := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
        (by linarith [hh.1] : 0 < h)) (sub_pos.mpr hu1)) (sub_pos.mpr hijr)
      nlinarith only [hprod]
    have hreturn : F (N₁ - 1) = F 0 := by
      unfold crossingPolynomial at hroot
      rw [if_pos rfl] at hroot
      simp only [F, pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero, mul_one]
      rw [huk]
      nlinarith only [hroot]
    have hdrop := after_return_decreases F u hu hanti (N₁ - 1) (N₂ - 1)
      (by omega) (by omega) hreturn
    have hF0 : F 0 = 1 := by simp [F]
    rw [hreturn, hF0] at hdrop
    unfold crossingPolynomial
    rw [if_pos rfl]
    change t ^ (2 * (N₂ - 1)) * (1 + 2 * ((N₂ - 1 : ℕ) : ℝ) * h) - 1 < 0
    rw [← huk]
    exact sub_neg.mpr hdrop
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    let b := base h q
    let v := (t / b) ^ 2
    have hb1 : 1 < b := by dsimp [b, base]; nlinarith [hh.1]
    have hbpos : 0 < b := by linarith
    have htv : 0 < t / b := div_pos ht hbpos
    have htvlt : t / b < t := by
      apply (div_lt_iff₀ hbpos).2
      nlinarith [mul_pos ht (sub_pos.mpr hb1)]
    have hv : 0 < v := pow_pos htv 2
    have hvu : v < u := by dsimp [v, u]; nlinarith
    have hv1 : v < 1 := lt_trans hvu hu1
    have hr : 0 < v / u := div_pos hv hu
    have hr1 : v / u < 1 := (div_lt_one hu).mpr hvu
    let F : ℕ → ℝ := fun n => (1 + q) * u ^ n - v ^ n
    have hnorm (n : ℕ) : (F (n + 1) - F n) / u ^ n =
        -(1 + q) * (1 - u) + (1 - v) * (v / u) ^ n := by
      dsimp [F]
      rw [pow_succ, pow_succ, div_pow]
      field_simp [(pow_pos hu n).ne']
      ring
    have hanti : StrictAnti (fun n => (F (n + 1) - F n) / u ^ n) := by
      intro i j hij
      change (F (j + 1) - F j) / u ^ j < (F (i + 1) - F i) / u ^ i
      rw [hnorm i, hnorm j]
      have hp := pow_lt_pow_right_of_lt_one₀ hr hr1 hij
      have hprod := mul_pos (sub_pos.mpr hv1) (sub_pos.mpr hp)
      nlinarith only [hprod]
    have hpoly (N : ℕ) : crossingPolynomial N q h =
        b ^ (2 * (N - 1)) * (F (N - 1) - q) := by
      unfold crossingPolynomial
      rw [if_neg hz]
      change t ^ (2 * (N - 1)) * ((1 + q) * b ^ (2 * (N - 1)) - 1) -
        q * b ^ (2 * (N - 1)) = b ^ (2 * (N - 1)) *
          ((1 + q) * u ^ (N - 1) - v ^ (N - 1) - q)
      rw [huk]
      have hvk (n : ℕ) : v ^ n = t ^ (2 * n) / b ^ (2 * n) := by
        dsimp [v]
        rw [← pow_mul, div_pow]
      rw [hvk]
      field_simp [(pow_pos hbpos (2 * (N - 1))).ne']
    have hreturn : F (N₁ - 1) = F 0 := by
      rw [hpoly] at hroot
      have heq := (mul_eq_zero.mp hroot).resolve_left (pow_pos hbpos _).ne'
      have hF0 : F 0 = q := by simp [F]
      rw [hF0]
      exact sub_eq_zero.mp heq
    have hdrop := after_return_decreases F u hu hanti (N₁ - 1) (N₂ - 1)
      (by omega) (by omega) hreturn
    have hF0 : F 0 = q := by simp [F]
    rw [hreturn, hF0] at hdrop
    rw [hpoly]
    exact mul_neg_of_pos_of_neg (pow_pos hbpos _) (sub_neg.mpr hdrop)

theorem solution : StepMonotonicityClaim := by
  exact ⟨optimum_q_strict, optimum_N_strict⟩


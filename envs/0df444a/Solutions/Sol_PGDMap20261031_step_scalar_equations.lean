-- Prove2me | solution 1 for PGDMap20261031.step_scalar_equations
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T14:45:53.264283+00:00
-- url     : https://prove2.me/submissions/87fef4f9-c8fd-43a8-8505-2bd8d9dfd76c

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Stepsize
import Theorems.Thm_PGDMap20261031_step_balance

open PGDMap20261031
noncomputable section

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

theorem solution : StepRootEquationsClaim := by
  intro N q h hN hq hlo hhi
  have hbalance := PGDMap20261031.step_balance N q hN hq
  have hiff : h = optimalStep N q ↔ branchA N h q = branchB N h q := by
    constructor
    · intro heq
      subst h
      exact hbalance.2.2.2.1
    · exact hbalance.2.2.2.2 h hlo hhi
  rw [hiff, crossing_iff N q h hN hq ⟨hlo, hhi⟩]
  by_cases hz : q = 0
  · simp only [if_pos hz, crossingPolynomial]
    constructor <;> intro heq <;> linarith only [heq]
  · rw [if_neg hz]
    unfold crossingPolynomial
    rw [if_neg hz]
    have hzpow : (base h q) ^ (-(2 * ((N - 1 : ℕ) : ℤ))) =
        ((base h q) ^ (2 * (N - 1)))⁻¹ := by
      rw [show (2 : ℤ) * ((N - 1 : ℕ) : ℤ) = ((2 * (N - 1) : ℕ) : ℤ) by push_cast; ring]
      rw [zpow_neg, zpow_natCast]
    rw [hzpow]
    have hb : 1 ≤ base h q := by unfold base; nlinarith
    have hPge := one_le_pow₀ hb (n := 2 * (N - 1))
    generalize hPdef : (base h q) ^ (2 * (N - 1)) = P at hPge ⊢
    have hPpos : 0 < P := by linarith
    have hInv : P⁻¹ ≤ 1 := by
      rw [← one_div]
      apply (div_le_iff₀ hPpos).2
      linarith
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    have hden : 0 < 1 + q - P⁻¹ := by linarith
    rw [eq_div_iff hden.ne']
    field_simp [hPpos.ne']
    constructor <;> intro heq <;> nlinarith only [heq]


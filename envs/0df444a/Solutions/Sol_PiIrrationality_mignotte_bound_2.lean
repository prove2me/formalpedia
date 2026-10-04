-- Prove2me | solution 2 for PiIrrationality.mignotte_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T14:35:59.838934+00:00
-- url     : https://prove2.me/submissions/e215c7a6-affc-4e80-85ea-8a24073d124b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_MediumPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/- Source component: MahlerReference.lean -/
section Component_MahlerReference

section PartLcm

/-!
# Bounds for `lcm(1, …, n)`

We define `lcmUpTo n = lcm(1, …, n)` and prove `lcmUpTo n ≤ 3 ^ n` for `n ≤ 200`
(by computation) and `lcmUpTo n ≤ 3.49 ^ n` for all `n` (Chebyshev-type argument based on
`lcm(1..6k) ∣ lcm(1..k) * (6k)! / ((3k)! (2k)! k!)`).
-/

namespace PiMahler

/-- `lcmUpTo n = lcm(1, …, n)`. -/
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUpTo n) (n + 1)

lemma lcmUpTo_pos : ∀ n, 0 < lcmUpTo n
  | 0 => by simp [lcmUpTo]
  | n + 1 => by
    simp only [lcmUpTo]
    exact Nat.lcm_pos (lcmUpTo_pos n) (Nat.succ_pos n)

lemma dvd_lcmUpTo : ∀ n i, 1 ≤ i → i ≤ n → i ∣ lcmUpTo n
  | 0, i, h1, h2 => by omega
  | n + 1, i, h1, h2 => by
    simp only [lcmUpTo]
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (dvd_lcmUpTo n i h1 (by omega)).trans (Nat.dvd_lcm_left _ _)
    · have : i = n + 1 := by omega
      subst this
      exact Nat.dvd_lcm_right _ _

lemma lcmUpTo_dvd : ∀ n X, (∀ i, 1 ≤ i → i ≤ n → i ∣ X) → lcmUpTo n ∣ X
  | 0, X, _ => by simp [lcmUpTo]
  | n + 1, X, h => by
    simp only [lcmUpTo]
    exact Nat.lcm_dvd (lcmUpTo_dvd n X fun i h1 h2 => h i h1 (by omega)) (h _ (by omega) le_rfl)

lemma lcmUpTo_dvd_of_le {n n' : ℕ} (h : n ≤ n') : lcmUpTo n ∣ lcmUpTo n' :=
  lcmUpTo_dvd n _ fun i h1 h2 => dvd_lcmUpTo n' i h1 (h2.trans h)

lemma lcmUpTo_le_of_le {n n' : ℕ} (h : n ≤ n') : lcmUpTo n ≤ lcmUpTo n' :=
  Nat.le_of_dvd (lcmUpTo_pos _) (lcmUpTo_dvd_of_le h)

/-- The multinomial coefficient `(6k)! / ((3k)! (2k)! k!)`. -/
def M6 (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose (2 * k)

lemma choose_mul_pow_le_add_pow (n r x y : ℕ) (h : r ≤ n) :
    n.choose r * (x ^ r * y ^ (n - r)) ≤ (x + y) ^ n := by
  rw [add_pow]
  have := Finset.single_le_sum (f := fun m => x ^ m * y ^ (n - m) * (n.choose m))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le h))
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma M6_le (k : ℕ) : M6 k ≤ 432 ^ k := by
  have h1 := choose_mul_pow_le_add_pow (6 * k) (3 * k) 3 3 (by omega)
  have h2 := choose_mul_pow_le_add_pow (3 * k) (2 * k) 2 1 (by omega)
  have e1 : 6 * k - 3 * k = 3 * k := by omega
  have e2 : 3 * k - 2 * k = k := by omega
  rw [e1] at h1
  rw [e2, one_pow, mul_one] at h2
  -- M6 k * (4^k * 27^k) ≤ 6^(6k) = 46656^k = 432^k * 108^k
  have key : M6 k * 108 ^ k ≤ 432 ^ k * 108 ^ k := by
    have : M6 k * (2 ^ (2 * k) * 3 ^ (3 * k)) ≤ (3 + 3) ^ (6 * k) := by
      unfold M6
      calc (6 * k).choose (3 * k) * (3 * k).choose (2 * k) * (2 ^ (2 * k) * 3 ^ (3 * k))
          = (6 * k).choose (3 * k) * (((3 * k).choose (2 * k) * 2 ^ (2 * k)) * 3 ^ (3 * k)) := by
            ring
        _ ≤ (6 * k).choose (3 * k) * ((2 + 1) ^ (3 * k) * 3 ^ (3 * k)) := by gcongr
        _ = (6 * k).choose (3 * k) * (3 ^ (3 * k) * 3 ^ (3 * k)) := by norm_num
        _ ≤ (3 + 3) ^ (6 * k) := h1
    have e3 : (2 : ℕ) ^ (2 * k) * 3 ^ (3 * k) = 108 ^ k := by
      rw [pow_mul, pow_mul, ← mul_pow]; norm_num
    have e4 : ((3 : ℕ) + 3) ^ (6 * k) = 432 ^ k * 108 ^ k := by
      rw [pow_mul, ← mul_pow]; norm_num
    rw [e3, e4] at this
    exact this
  exact Nat.le_of_mul_le_mul_right key (by positivity)

lemma M6_mul_factorials (k : ℕ) :
    M6 k * ((3 * k).factorial * (2 * k).factorial * k.factorial) = (6 * k).factorial := by
  unfold M6
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := 2 * k) (by omega)
  have e1 : 6 * k - 3 * k = 3 * k := by omega
  have e2 : 3 * k - 2 * k = k := by omega
  rw [e1] at h1
  rw [e2] at h2
  rw [← h1, ← h2]
  ring

/-- The key floor inequality `⌊3x⌋ + ⌊2x⌋ + ⌊x⌋ + [1/6 ≤ x < 1] ≤ ⌊6x⌋`. -/
lemma floor_ineq (k c : ℕ) (hc : 0 < c) :
    3 * k / c + 2 * k / c + k / c + (if k < c ∧ c ≤ 6 * k then 1 else 0) ≤ 6 * k / c := by
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hk0 : k / c = 0 := Nat.div_eq_of_lt h1
    rw [hk0]
    set A := 3 * k / c with hA
    set B := 2 * k / c with hB
    have hA2 : A < 3 := by
      rw [hA, Nat.div_lt_iff_lt_mul hc]; omega
    have hB2 : B < 2 := by
      rw [hB, Nat.div_lt_iff_lt_mul hc]; omega
    have hAc : A * c ≤ 3 * k := Nat.div_mul_le_self _ _
    have hBc : B * c ≤ 2 * k := Nat.div_mul_le_self _ _
    rw [Nat.le_div_iff_mul_le hc]
    interval_cases A <;> interval_cases B <;> omega
  · rw [add_zero, Nat.le_div_iff_mul_le hc]
    have h1 : 3 * k / c * c ≤ 3 * k := Nat.div_mul_le_self _ _
    have h2 : 2 * k / c * c ≤ 2 * k := Nat.div_mul_le_self _ _
    have h3 : k / c * c ≤ k := Nat.div_mul_le_self _ _
    nlinarith

lemma factorization_M6_ge (k p : ℕ) (hp : p.Prime) (hk : 0 < k) (a : ℕ) (ha : p ^ a ≤ 6 * k) :
    a - Nat.log p k ≤ (M6 k).factorization p := by
  set B := Nat.log p (6 * k) + 1 with hB
  have hlog : ∀ x, x ≤ 6 * k → Nat.log p x < B := fun x hx => by
    have := Nat.log_mono_right (b := p) hx; omega
  have hM0 : M6 k ≠ 0 := by
    intro h; have := M6_mul_factorials k; rw [h, zero_mul] at this
    exact Nat.factorial_ne_zero _ this.symm
  have hfac := congrArg (fun x => x.factorization p) (M6_mul_factorials k)
  beta_reduce at hfac
  rw [Nat.factorization_mul hM0 (by positivity), Nat.factorization_mul (by positivity)
    (by positivity), Nat.factorization_mul (by positivity) (by positivity)] at hfac
  simp only [Finsupp.coe_add, Pi.add_apply] at hfac
  rw [Nat.factorization_factorial hp (hlog _ le_rfl),
    Nat.factorization_factorial hp (hlog (3 * k) (by omega)),
    Nat.factorization_factorial hp (hlog (2 * k) (by omega)),
    Nat.factorization_factorial hp (hlog k (by omega))] at hfac
  -- termwise inequality
  have hterm : ∀ i ∈ Finset.Ico 1 B, 3 * k / p ^ i + 2 * k / p ^ i + k / p ^ i +
      (if k < p ^ i ∧ p ^ i ≤ 6 * k then 1 else 0) ≤ 6 * k / p ^ i :=
    fun i _ => floor_ineq k (p ^ i) (pow_pos hp.pos i)
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib] at hsum
  -- the indicator sum is at least a - log p k
  have hind : a - Nat.log p k ≤ ∑ i ∈ Finset.Ico 1 B,
      (if k < p ^ i ∧ p ^ i ≤ 6 * k then 1 else 0) := by
    have hsub : Finset.Ico (Nat.log p k + 1) (a + 1) ⊆
        (Finset.Ico 1 B).filter (fun i => k < p ^ i ∧ p ^ i ≤ 6 * k) := by
      intro i hi
      simp only [Finset.mem_Ico] at hi
      simp only [Finset.mem_filter, Finset.mem_Ico]
      have hpa : p ^ i ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
      have hlt : k < p ^ i := by
        have := Nat.lt_pow_succ_log_self hp.one_lt k
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right hp.pos (by omega))
      have haB : a < B := by
        have : a ≤ Nat.log p (6 * k) := by
          exact (Nat.le_log_iff_pow_le hp.one_lt (by omega)).2 ha
        omega
      refine ⟨⟨by omega, by omega⟩, hlt, hpa.trans ha⟩
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at this
    omega
  omega

lemma lcmUpTo_six_dvd (k : ℕ) : lcmUpTo (6 * k) ∣ lcmUpTo k * M6 k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [lcmUpTo]
  have hM0 : M6 k ≠ 0 := by
    intro h; have := M6_mul_factorials k; rw [h, zero_mul] at this
    exact Nat.factorial_ne_zero _ this.symm
  have hL0 : lcmUpTo k ≠ 0 := (lcmUpTo_pos k).ne'
  apply lcmUpTo_dvd
  intro i hi1 hi2
  rw [← Nat.factorization_le_iff_dvd (by omega) (mul_ne_zero hL0 hM0)]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul hL0 hM0]
    simp only [Finsupp.coe_add, Pi.add_apply]
    set a := i.factorization p with ha
    have hpa : p ^ a ≤ 6 * k := by
      have : p ^ a ∣ i := (hp.pow_dvd_iff_le_factorization (by omega)).2 le_rfl
      exact (Nat.le_of_dvd (by omega) this).trans hi2
    have h1 := factorization_M6_ge k p hp hk a hpa
    -- p ^ min a (log p k) divides lcmUpTo k
    have h2 : min a (Nat.log p k) ≤ (lcmUpTo k).factorization p := by
      rw [← hp.pow_dvd_iff_le_factorization hL0]
      apply dvd_lcmUpTo
      · exact Nat.one_le_pow _ _ hp.pos
      · exact (Nat.pow_le_pow_right hp.pos (min_le_right _ _)).trans
          (Nat.pow_log_le_self p (by omega))
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Computational check used for small `n`. -/
def checkLcm3 : ℕ → Bool
  | 0 => true
  | n + 1 => decide (lcmUpTo (n + 1) ≤ 3 ^ (n + 1)) && checkLcm3 n

lemma checkLcm3_spec : ∀ N, checkLcm3 N = true → ∀ n ≤ N, lcmUpTo n ≤ 3 ^ n
  | 0, _, n, hn => by
    have : n = 0 := by omega
    subst this; simp [lcmUpTo]
  | N + 1, h, n, hn => by
    simp only [checkLcm3, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_or_ge n (N + 1) with h' | h'
    · exact checkLcm3_spec N h.2 n (by omega)
    · have : n = N + 1 := by omega
      subst this; exact h.1

set_option maxRecDepth 100000 in
lemma checkLcm3_200 : checkLcm3 200 = true := by decide

theorem lcmUpTo_le_three_pow {n : ℕ} (hn : n ≤ 200) : lcmUpTo n ≤ 3 ^ n :=
  checkLcm3_spec 200 checkLcm3_200 n hn

theorem lcmUpTo_le_real (n : ℕ) : (lcmUpTo n : ℝ) ≤ (3.49 : ℝ) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge 200 n with hn | hn
  · set k := (n + 5) / 6 with hk
    have hk1 : n ≤ 6 * k := by omega
    have hk2 : 6 * k ≤ n + 5 := by omega
    have hk3 : 34 ≤ k := by omega
    have hkn : k < n := by omega
    have hstep : (lcmUpTo n : ℝ) ≤ (lcmUpTo k : ℝ) * 432 ^ k := by
      have h1 : lcmUpTo n ≤ lcmUpTo k * M6 k :=
        (lcmUpTo_le_of_le hk1).trans (Nat.le_of_dvd (Nat.mul_pos (lcmUpTo_pos k)
          (Nat.pos_of_ne_zero (fun h => by
            have := M6_mul_factorials k; rw [h, zero_mul] at this
            exact Nat.factorial_ne_zero _ this.symm))) (lcmUpTo_six_dvd k))
      have h2 : lcmUpTo k * M6 k ≤ lcmUpTo k * 432 ^ k := Nat.mul_le_mul_left _ (M6_le k)
      exact_mod_cast h1.trans h2
    have hpow : (3.49 : ℝ) ^ (6 * k) ≤ (3.49 : ℝ) ^ 5 * (3.49 : ℝ) ^ n := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h6 : (3.49 : ℝ) ^ (6 * k) = ((3.49 : ℝ) ^ 6) ^ k := by rw [pow_mul]
    rcases Nat.lt_or_ge 200 k with hk200 | hk200
    · -- use the induction hypothesis
      have hih := ih k hkn
      have hc : (3.49 : ℝ) ^ 5 ≤ ((3.49 : ℝ) ^ 5 / 432) ^ k := by
        calc (3.49 : ℝ) ^ 5 ≤ ((3.49 : ℝ) ^ 5 / 432) ^ 200 := by norm_num
          _ ≤ ((3.49 : ℝ) ^ 5 / 432) ^ k := pow_le_pow_right₀ (by norm_num) hk200.le
      have : (lcmUpTo k : ℝ) * 432 ^ k ≤ (3.49 : ℝ) ^ n := by
        have e : ((3.49 : ℝ) ^ 6) ^ k = (3.49 : ℝ) ^ k * 432 ^ k * ((3.49 : ℝ) ^ 5 / 432) ^ k := by
          rw [← mul_pow, ← mul_pow]; congr 1; ring
        have hpos : (0 : ℝ) < (3.49 : ℝ) ^ 5 := by positivity
        have : (3.49 : ℝ) ^ k * 432 ^ k * (3.49 : ℝ) ^ 5 ≤ (3.49 : ℝ) ^ 5 * (3.49 : ℝ) ^ n := by
          calc (3.49 : ℝ) ^ k * 432 ^ k * (3.49 : ℝ) ^ 5
              ≤ (3.49 : ℝ) ^ k * 432 ^ k * ((3.49 : ℝ) ^ 5 / 432) ^ k := by gcongr
            _ = (3.49 : ℝ) ^ (6 * k) := by rw [h6, e]
            _ ≤ _ := hpow
        have h' : (3.49 : ℝ) ^ k * 432 ^ k ≤ (3.49 : ℝ) ^ n := by
          by_contra hc'
          push_neg at hc'
          have := mul_lt_mul_of_pos_left hc' hpos
          linarith
        calc (lcmUpTo k : ℝ) * 432 ^ k ≤ (3.49 : ℝ) ^ k * 432 ^ k := by gcongr
          _ ≤ _ := h'
      exact hstep.trans this
    · have hl : (lcmUpTo k : ℝ) ≤ 3 ^ k := by exact_mod_cast lcmUpTo_le_three_pow hk200
      have hc : (3.49 : ℝ) ^ 5 ≤ ((3.49 : ℝ) ^ 6 / 1296) ^ k := by
        calc (3.49 : ℝ) ^ 5 ≤ ((3.49 : ℝ) ^ 6 / 1296) ^ 34 := by norm_num
          _ ≤ ((3.49 : ℝ) ^ 6 / 1296) ^ k := pow_le_pow_right₀ (by norm_num) hk3
      have hpos : (0 : ℝ) < (3.49 : ℝ) ^ 5 := by positivity
      have e : ((3.49 : ℝ) ^ 6) ^ k = (1296 : ℝ) ^ k * ((3.49 : ℝ) ^ 6 / 1296) ^ k := by
        rw [← mul_pow]; congr 1; ring
      have : (1296 : ℝ) ^ k * (3.49 : ℝ) ^ 5 ≤ (3.49 : ℝ) ^ 5 * (3.49 : ℝ) ^ n := by
        calc (1296 : ℝ) ^ k * (3.49 : ℝ) ^ 5 ≤ (1296 : ℝ) ^ k * ((3.49 : ℝ) ^ 6 / 1296) ^ k := by
              gcongr
          _ = (3.49 : ℝ) ^ (6 * k) := by rw [h6, e]
          _ ≤ _ := hpow
      have h' : (1296 : ℝ) ^ k ≤ (3.49 : ℝ) ^ n := by
        by_contra hc'
        push_neg at hc'
        have := mul_lt_mul_of_pos_left hc' hpos
        linarith
      calc (lcmUpTo n : ℝ) ≤ (lcmUpTo k : ℝ) * 432 ^ k := hstep
        _ ≤ 3 ^ k * 432 ^ k := by gcongr
        _ = (1296 : ℝ) ^ k := by rw [← mul_pow]; norm_num
        _ ≤ _ := h'
  · calc (lcmUpTo n : ℝ) ≤ 3 ^ n := by exact_mod_cast lcmUpTo_le_three_pow hn
      _ ≤ (3.49 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n

end PiMahler

end PartLcm

section PartAlgebra

/-!
# Algebraic core: the residue functional

Nodes form a finite set `S ⊆ ℤ`, each with multiplicity `m + 1`.
`Lam m S F = ∑_{j ∈ S} [u^m] (F(j+u) · P_j(u))` where `P_j(u) = ∏_{k ≠ j} (j - k + u)^{-(m+1)}`.
This is the sum of residues of `F(t) / Q(t)` with `Q(t) = ∏_{j∈S} (t - j)^{m+1}`.
-/

namespace PiMahler

open Polynomial

variable (m : ℕ) (S : Finset ℤ)

/-- `Q(t) = ∏_{k ∈ S} (t - k)^(m+1)`. -/
noncomputable def Qp : ℚ[X] := ∏ k ∈ S, (X - C (k : ℚ)) ^ (m + 1)

/-- `Q_j(t) = ∏_{k ∈ S, k ≠ j} (t - k)^(m+1)`. -/
noncomputable def Qj (j : ℤ) : ℚ[X] := ∏ k ∈ S.erase j, (X - C (k : ℚ)) ^ (m + 1)

/-- Taylor shift `F(X + j)`. -/
noncomputable def shiftP (j : ℤ) (F : ℚ[X]) : ℚ[X] := F.comp (X + C (j : ℚ))

/-- Power series of `1 / (a + u)`. -/
noncomputable def invLin (a : ℚ) : PowerSeries ℚ := PowerSeries.mk fun e => (-1) ^ e / a ^ (e + 1)

/-- `P_j(u) = ∏_{k ≠ j} (j - k + u)^{-(m+1)}`. -/
noncomputable def Pj (j : ℤ) : PowerSeries ℚ :=
  ∏ k ∈ S.erase j, (invLin ((j : ℚ) - k)) ^ (m + 1)

/-- The residue functional. -/
noncomputable def Lam (F : ℚ[X]) : ℚ :=
  ∑ j ∈ S, PowerSeries.coeff m (((shiftP j F : ℚ[X]) : PowerSeries ℚ) * Pj m S j)

variable {m S}

lemma shiftP_mul (j : ℤ) (F G : ℚ[X]) : shiftP j (F * G) = shiftP j F * shiftP j G := by
  simp [shiftP, mul_comp]

lemma shiftP_pow (j : ℤ) (F : ℚ[X]) (n : ℕ) : shiftP j (F ^ n) = shiftP j F ^ n := by
  simp [shiftP, pow_comp]

lemma shiftP_add (j : ℤ) (F G : ℚ[X]) : shiftP j (F + G) = shiftP j F + shiftP j G := by
  simp [shiftP, add_comp]

lemma shiftP_sub (j : ℤ) (F G : ℚ[X]) : shiftP j (F - G) = shiftP j F - shiftP j G := by
  simp [shiftP, sub_comp]

lemma shiftP_C (j : ℤ) (a : ℚ) : shiftP j (C a) = C a := by simp [shiftP]

lemma shiftP_X_sub_C (j k : ℤ) : shiftP j (X - C (k : ℚ)) = X + C ((j : ℚ) - k) := by
  simp only [shiftP, sub_comp, X_comp, C_comp, map_sub]; ring

lemma shiftP_X_pow (j : ℤ) (n : ℕ) : shiftP j (X ^ n) = (X + C (j : ℚ)) ^ n := by
  simp [shiftP]

lemma shiftP_prod (j : ℤ) (T : Finset ℤ) (f : ℤ → ℚ[X]) :
    shiftP j (∏ k ∈ T, f k) = ∏ k ∈ T, shiftP j (f k) := by
  simp only [shiftP]
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comp, ih]

lemma shiftP_sum (j : ℤ) (T : Finset ℕ) (f : ℕ → ℚ[X]) :
    shiftP j (∑ k ∈ T, f k) = ∑ k ∈ T, shiftP j (f k) := by
  simp only [shiftP]
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comp, ih]

lemma unshift (j : ℤ) (F : ℚ[X]) : (shiftP j F).comp (X - C (j : ℚ)) = F := by
  simp [shiftP, comp_assoc]

lemma dvd_iff_X_pow_dvd_shift (j : ℤ) (n : ℕ) (G : ℚ[X]) :
    (X - C (j : ℚ)) ^ n ∣ G ↔ X ^ n ∣ shiftP j G := by
  constructor
  · rintro ⟨H, rfl⟩
    refine ⟨shiftP j H, ?_⟩
    rw [shiftP_mul, shiftP_pow]
    simp [shiftP]
  · rintro ⟨H, hH⟩
    refine ⟨H.comp (X - C (j : ℚ)), ?_⟩
    have := congrArg (fun P => P.comp (X - C (j : ℚ))) hH
    simp only [unshift, mul_comp, pow_comp, X_comp] at this
    exact this

lemma invLin_mul {a : ℚ} (ha : a ≠ 0) :
    (((X + C a : ℚ[X])) : PowerSeries ℚ) * invLin a = 1 := by
  ext n
  rw [Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, add_mul]
  rcases n with _ | n
  · simp [invLin, ha]
  · rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    simp only [invLin, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    simp only [Nat.succ_ne_zero, if_false]
    field_simp
    ring

lemma coe_prod (T : Finset ℤ) (f : ℤ → ℚ[X]) :
    (((∏ k ∈ T, f k : ℚ[X])) : PowerSeries ℚ) = ∏ k ∈ T, ((f k : ℚ[X]) : PowerSeries ℚ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.coe_mul, ih]

lemma card_arith (c : ℕ) (hc : 1 ≤ c) : (m + 1) * (c - 1) + m = (m + 1) * c - 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.mul_succ]; omega

lemma coeff_mul_congr_low (A B B' : PowerSeries ℚ) (n : ℕ)
    (h : ∀ y < n, PowerSeries.coeff y B = PowerSeries.coeff y B') :
    ∀ d < n, PowerSeries.coeff d (A * B) = PowerSeries.coeff d (A * B') := by
  intro d hd
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [h p.2 (by omega)]

lemma shift_Qj_mul_Pj {j : ℤ} :
    ((shiftP j (Qj m S j) : ℚ[X]) : PowerSeries ℚ) * Pj m S j = 1 := by
  unfold Qj Pj
  rw [shiftP_prod, coe_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k hk
  have hkj : (j : ℚ) - k ≠ 0 := by
    have := Finset.ne_of_mem_erase hk
    intro h; apply this; exact_mod_cast (sub_eq_zero.1 h).symm
  rw [shiftP_pow, shiftP_X_sub_C, Polynomial.coe_pow, ← mul_pow, invLin_mul hkj, one_pow]

lemma Qp_eq_mul {j : ℤ} (hj : j ∈ S) : Qp m S = (X - C (j : ℚ)) ^ (m + 1) * Qj m S j := by
  unfold Qp Qj
  exact (Finset.mul_prod_erase S (fun k : ℤ => (X - C (k : ℚ)) ^ (m + 1)) hj).symm

lemma Qj_monic (j : ℤ) : (Qj m S j).Monic := by
  unfold Qj
  exact monic_prod_of_monic _ _ fun k _ => (monic_X_sub_C _).pow _

lemma natDegree_Qj (j : ℤ) : (Qj m S j).natDegree = (m + 1) * (S.erase j).card := by
  unfold Qj
  rw [natDegree_prod_of_monic _ _ fun k _ => (monic_X_sub_C _).pow _]
  rw [Finset.sum_congr rfl (fun k _ => by rw [natDegree_pow, natDegree_X_sub_C, mul_one])]
  simp [mul_comm]

lemma Qp_monic : (Qp m S).Monic := by
  unfold Qp
  exact monic_prod_of_monic _ _ fun k _ => (monic_X_sub_C _).pow _

lemma natDegree_Qp : (Qp m S).natDegree = (m + 1) * S.card := by
  unfold Qp
  rw [natDegree_prod_of_monic _ _ fun k _ => (monic_X_sub_C _).pow _]
  rw [Finset.sum_congr rfl (fun k _ => by rw [natDegree_pow, natDegree_X_sub_C, mul_one])]
  simp [mul_comm]

lemma X_sub_C_pow_dvd_Qj {j k : ℤ} (hk : k ∈ S) (hkj : k ≠ j) :
    (X - C (k : ℚ)) ^ (m + 1) ∣ Qj m S j := by
  unfold Qj
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hkj, hk⟩)

/-- Coefficient `c_j e` of the local expansion. -/
noncomputable def locCoeff (F : ℚ[X]) (j : ℤ) (e : ℕ) : ℚ :=
  PowerSeries.coeff e (((shiftP j F : ℚ[X]) : PowerSeries ℚ) * Pj m S j)

/-- The polynomial `ρ_j = ∑_{e ≤ m} c_j e (X - j)^e`. -/
noncomputable def rho (F : ℚ[X]) (j : ℤ) : ℚ[X] :=
  ∑ e ∈ Finset.range (m + 1), C (locCoeff (m := m) (S := S) F j e) * (X - C (j : ℚ)) ^ e

lemma shiftP_rho (F : ℚ[X]) (j : ℤ) :
    shiftP j (rho (m := m) (S := S) F j) =
      ∑ e ∈ Finset.range (m + 1), C (locCoeff (m := m) (S := S) F j e) * X ^ e := by
  unfold rho
  rw [shiftP_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [shiftP_mul, shiftP_C, shiftP_pow]
  simp [shiftP]

lemma coeff_shiftP_rho (F : ℚ[X]) (j : ℤ) (y : ℕ) (hy : y < m + 1) :
    (shiftP j (rho (m := m) (S := S) F j)).coeff y = locCoeff (m := m) (S := S) F j y := by
  rw [shiftP_rho, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_range.2 hy) h

lemma natDegree_rho_le (F : ℚ[X]) (j : ℤ) : (rho (m := m) (S := S) F j).natDegree ≤ m := by
  unfold rho
  apply natDegree_sum_le_of_forall_le
  intro e he
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 he)

lemma coeff_rho_top (F : ℚ[X]) (j : ℤ) :
    (rho (m := m) (S := S) F j).coeff m = locCoeff (m := m) (S := S) F j m := by
  unfold rho
  rw [finset_sum_coeff, Finset.sum_range_succ]
  have hzero : ∀ e ∈ Finset.range m,
      (C (locCoeff (m := m) (S := S) F j e) * (X - C (j : ℚ)) ^ e).coeff m = 0 := by
    intro e he
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    exact Finset.mem_range.1 he
  rw [Finset.sum_eq_zero hzero, zero_add, coeff_C_mul]
  have : ((X - C (j : ℚ)) ^ m).coeff m = 1 := by
    have h := ((monic_X_sub_C (j : ℚ)).pow m)
    have hd : ((X - C (j : ℚ)) ^ m).natDegree = m := by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have h2 := h.coeff_natDegree; rwa [hd] at h2
  rw [this, mul_one]

lemma local_congr (F : ℚ[X]) {j : ℤ} :
    (X - C (j : ℚ)) ^ (m + 1) ∣ F - Qj m S j * rho (m := m) (S := S) F j := by
  rw [dvd_iff_X_pow_dvd_shift, X_pow_dvd_iff]
  intro d hd
  rw [shiftP_sub, shiftP_mul, coeff_sub, sub_eq_zero]
  rw [← Polynomial.coeff_coe, ← Polynomial.coeff_coe, Polynomial.coe_mul]
  rw [coeff_mul_congr_low _ _ (((shiftP j F : ℚ[X]) : PowerSeries ℚ) * Pj m S j) (m + 1)
    (fun y hy => by rw [Polynomial.coeff_coe, coeff_shiftP_rho F j y hy]; rfl) d hd]
  rw [mul_left_comm, shift_Qj_mul_Pj, mul_one]

theorem Lam_eq_coeff (hS : S.Nonempty) (F : ℚ[X]) (hF : F.natDegree < (m + 1) * S.card) :
    Lam m S F = F.coeff ((m + 1) * S.card - 1) := by
  set Δ := F - ∑ j ∈ S, Qj m S j * rho (m := m) (S := S) F j with hΔ
  have hdvd : ∀ k ∈ S, (X - C (k : ℚ)) ^ (m + 1) ∣ Δ := by
    intro k hk
    rw [hΔ, ← Finset.add_sum_erase _ _ hk]
    have h1 := local_congr (m := m) (S := S) F (j := k)
    have h2 : (X - C (k : ℚ)) ^ (m + 1) ∣
        ∑ j ∈ S.erase k, Qj m S j * rho (m := m) (S := S) F j :=
      Finset.dvd_sum fun j hj =>
        (X_sub_C_pow_dvd_Qj hk (Finset.ne_of_mem_erase hj).symm).mul_right _
    have : F - (Qj m S k * rho (m := m) (S := S) F k +
        ∑ j ∈ S.erase k, Qj m S j * rho (m := m) (S := S) F j) =
        (F - Qj m S k * rho (m := m) (S := S) F k) -
        ∑ j ∈ S.erase k, Qj m S j * rho (m := m) (S := S) F j := by ring
    rw [this]
    exact dvd_sub h1 h2
  have hQdvd : Qp m S ∣ Δ := by
    unfold Qp
    apply Finset.prod_dvd_of_coprime _ hdvd
    intro a _ b _ hab
    have := Polynomial.pairwise_coprime_X_sub_C (K := ℚ) (s := fun k : ℤ => (k : ℚ))
      Int.cast_injective hab
    exact this.pow
  have hcard : 1 ≤ S.card := Finset.card_pos.2 hS
  have hdeg : Δ.natDegree < (Qp m S).natDegree := by
    rw [natDegree_Qp]
    rw [hΔ]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hF ?_)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _
      (n := (m + 1) * S.card - 1) ?_) (by
        have : 0 < (m + 1) * S.card := Nat.mul_pos (Nat.succ_pos m) hcard
        omega)
    intro j hj
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_Qj, Finset.card_erase_of_mem hj]
    have := natDegree_rho_le (m := m) (S := S) F j
    have := card_arith (m := m) S.card hcard
    omega
  have hΔ0 : Δ = 0 := by
    by_contra h
    exact absurd (natDegree_le_of_dvd hQdvd h) (not_le.2 hdeg)
  have hF' : F = ∑ j ∈ S, Qj m S j * rho (m := m) (S := S) F j := by
    rw [hΔ] at hΔ0; exact sub_eq_zero.1 hΔ0
  conv_rhs => rw [hF']
  rw [finset_sum_coeff]
  unfold Lam
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : (m + 1) * S.card - 1 = (m + 1) * (S.erase j).card + m := by
    rw [Finset.card_erase_of_mem hj]
    exact (card_arith (m := m) S.card hcard).symm
  rw [e, coeff_mul_add_eq_of_natDegree_le (le_of_eq (natDegree_Qj j)) (natDegree_rho_le F j)]
  have hm : (Qj m S j).coeff ((m + 1) * (S.erase j).card) = 1 := by
    rw [← natDegree_Qj]; exact Qj_monic j
  rw [hm, one_mul, coeff_rho_top]
  rfl

theorem Lam_mul_Qp (F : ℚ[X]) : Lam m S (F * Qp m S) = 0 := by
  unfold Lam
  apply Finset.sum_eq_zero
  intro j hj
  rw [Qp_eq_mul hj, shiftP_mul, shiftP_mul, shiftP_pow, shiftP_X_sub_C]
  simp only [sub_self, map_zero, add_zero]
  rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  rw [show ∀ a b c d : PowerSeries ℚ, a * (b * c) * d = b * (a * c * d) by intros; ring]
  rw [PowerSeries.coeff_X_pow_mul']
  simp

lemma Lam_add (F G : ℚ[X]) : Lam m S (F + G) = Lam m S F + Lam m S G := by
  unfold Lam
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftP_add, Polynomial.coe_add, add_mul, map_add]

lemma Lam_C_mul (a : ℚ) (F : ℚ[X]) : Lam m S (C a * F) = a * Lam m S F := by
  unfold Lam
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftP_mul, shiftP_C, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc,
    PowerSeries.coeff_C_mul]

lemma Lam_sum (T : Finset ℕ) (f : ℕ → ℚ[X]) : Lam m S (∑ i ∈ T, f i) = ∑ i ∈ T, Lam m S (f i) := by
  induction T using Finset.induction_on with
  | empty => simp [Lam, shiftP]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lam_add, ih]

end PiMahler

end PartAlgebra

section PartAlgebra2

/-!
# Algebraic core, part 2: the moments `τ` and their bounds
-/

namespace PiMahler

open Polynomial

variable {m : ℕ} {S : Finset ℤ}

lemma Lam_X_pow_lt (hS : S.Nonempty) {l : ℕ} (hl : l < (m + 1) * S.card - 1) :
    Lam m S (X ^ l) = 0 := by
  rw [Lam_eq_coeff hS _ (by rw [natDegree_X_pow]; omega), coeff_X_pow]
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]; omega

lemma Lam_X_pow_N (hS : S.Nonempty) : Lam m S (X ^ ((m + 1) * S.card - 1)) = 1 := by
  have : 0 < (m + 1) * S.card := Nat.mul_pos (Nat.succ_pos m) (Finset.card_pos.2 hS)
  rw [Lam_eq_coeff hS _ (by rw [natDegree_X_pow]; omega), coeff_X_pow]
  simp

/-- The generating series of the moments `E s = Λ(X^(N+s))`. -/
noncomputable def Eser (m : ℕ) (S : Finset ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun s => Lam m S (X ^ ((m + 1) * S.card - 1 + s))

/-- Reversed `Q`. -/
noncomputable def Qt (m : ℕ) (S : Finset ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun i => if i ≤ (m + 1) * S.card then (Qp m S).coeff ((m + 1) * S.card - i) else 0

lemma Lam_of_coeff_zero (hS : S.Nonempty) (G : ℚ[X])
    (hG : ∀ k, (m + 1) * S.card - 1 ≤ k → G.coeff k = 0) : Lam m S G = 0 := by
  have hpos : 0 < (m + 1) * S.card := Nat.mul_pos (Nat.succ_pos m) (Finset.card_pos.2 hS)
  by_cases h0 : G = 0
  · subst h0; simp [Lam, shiftP]
  have hdeg : G.natDegree < (m + 1) * S.card - 1 := by
    by_contra hc
    push_neg at hc
    exact (leadingCoeff_ne_zero.2 h0) (hG _ hc)
  rw [Lam_eq_coeff hS G (by omega)]
  exact hG _ le_rfl

theorem Eser_mul_Qt (hS : S.Nonempty) : Eser m S * Qt m S = 1 := by
  set N1 := (m + 1) * S.card with hN1
  have hpos : 0 < N1 := Nat.mul_pos (Nat.succ_pos m) (Finset.card_pos.2 hS)
  ext s
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Eser, Qt, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, if_true,
      Nat.zero_le, add_zero]
    rw [Lam_X_pow_N hS, ← natDegree_Qp, Qp_monic.coeff_natDegree, mul_one]
  · rw [if_neg (by omega)]
    -- turn the sum into `Λ G` for an explicit polynomial `G`
    set G : ℚ[X] := ∑ a ∈ Finset.range (s + 1),
      C (if s - a ≤ N1 then (Qp m S).coeff (N1 - (s - a)) else 0) * X ^ (N1 - 1 + a) with hG
    have hsum : ∑ a ∈ Finset.range (s + 1), Lam m S (X ^ (N1 - 1 + a)) *
        (if s - a ≤ N1 then (Qp m S).coeff (N1 - (s - a)) else 0) = Lam m S G := by
      rw [hG, Lam_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Lam_C_mul, mul_comm]
    rw [hsum]
    -- `G - X^(s-1) Q` has no coefficients in degrees `≥ N`
    have hdiff : Lam m S (G - X ^ (s - 1) * Qp m S) = 0 := by
      apply Lam_of_coeff_zero hS
      intro k hk
      rw [← hN1] at hk
      rw [coeff_sub, hG, finset_sum_coeff]
      simp only [coeff_C_mul, coeff_X_pow]
      rw [coeff_X_pow_mul']
      -- the sum has a single possibly nonzero term `a = k - (N1 - 1)`
      by_cases hka : k - (N1 - 1) < s + 1
      · rw [Finset.sum_eq_single (k - (N1 - 1))]
        · rw [if_pos (show k = N1 - 1 + (k - (N1 - 1)) by omega), mul_one]
          by_cases hsk : s - 1 ≤ k
          · rw [if_pos hsk, if_pos (show s - (k - (N1 - 1)) ≤ N1 by omega)]
            have : N1 - (s - (k - (N1 - 1))) = k - (s - 1) := by omega
            rw [this, sub_self]
          · rw [if_neg hsk, if_neg (show ¬ (s - (k - (N1 - 1)) ≤ N1) by omega), sub_zero]
        · intro b _ hb
          rw [if_neg (show ¬ k = N1 - 1 + b by omega), mul_zero]
        · intro h; exact absurd (Finset.mem_range.2 hka) h
      · rw [Finset.sum_eq_zero]
        · rw [zero_sub, neg_eq_zero]
          split_ifs with h2
          · apply coeff_eq_zero_of_natDegree_lt
            rw [natDegree_Qp]; omega
          · rfl
        · intro b hb
          rw [Finset.mem_range] at hb
          rw [if_neg (show ¬ k = N1 - 1 + b by omega), mul_zero]
    have hQ : Lam m S (X ^ (s - 1) * Qp m S) = 0 := Lam_mul_Qp _
    have : G = (G - X ^ (s - 1) * Qp m S) + X ^ (s - 1) * Qp m S := by ring
    rw [this, Lam_add, hdiff, hQ, add_zero]

/-- Geometric series `∑ a^k u^k`. -/
noncomputable def geom (a : ℚ) : PowerSeries ℚ := PowerSeries.mk fun k => a ^ k

lemma one_sub_mul_geom (a : ℚ) : (((1 - C a * X : ℚ[X])) : PowerSeries ℚ) * geom a = 1 := by
  ext n
  rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X, sub_mul, one_mul, map_sub]
  rcases n with _ | n
  · simp [geom]
  · rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    simp [geom, pow_succ]; ring

lemma reflect_pow_le (p : ℚ[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    ∀ n : ℕ, reflect (n * d) (p ^ n) = (reflect d p) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ, show (n + 1) * d = n * d + d by ring]
    rw [reflect_mul _ _ (by
      refine (natDegree_pow_le).trans ?_
      exact Nat.mul_le_mul_left n hp) hp]
    rw [reflect_pow_le p d hp n]

lemma reflect_X_sub_C (a : ℚ) : reflect 1 (X - C a) = 1 - C a * X := by
  ext i
  rw [coeff_reflect]
  rcases i with _ | _ | i
  · simp [revAt_le]
  · simp [revAt_le, coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_one]

lemma reflect_prod (T : Finset ℤ) :
    reflect ((m + 1) * T.card) (∏ k ∈ T, (X - C (k : ℚ)) ^ (m + 1)) =
      ∏ k ∈ T, (1 - C (k : ℚ) * X) ^ (m + 1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      show (m + 1) * (T.card + 1) = (m + 1) * 1 + (m + 1) * T.card by ring]
    rw [reflect_mul _ _ (F := (m + 1) * 1) (G := (m + 1) * T.card)]
    · rw [ih, reflect_pow_le _ 1 (by rw [natDegree_X_sub_C]) (m + 1), reflect_X_sub_C]
    · rw [natDegree_pow, natDegree_X_sub_C]
    · rw [natDegree_prod_of_monic _ _ fun k _ => (monic_X_sub_C _).pow _]
      rw [Finset.sum_congr rfl (fun k _ => by rw [natDegree_pow, natDegree_X_sub_C, mul_one])]
      simp [mul_comm]

lemma Qt_eq : Qt m S = (((∏ k ∈ S, (1 - C (k : ℚ) * X) ^ (m + 1) : ℚ[X])) : PowerSeries ℚ) := by
  rw [← reflect_prod]
  ext i
  rw [Polynomial.coeff_coe, coeff_reflect]
  simp only [Qt, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [revAt_le h]; rfl
  · rw [revAt_eq_self_of_lt (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_Qp (m := m) (S := S)
    unfold Qp at this
    omega

theorem Eser_eq (hS : S.Nonempty) : Eser m S = ∏ k ∈ S, (geom (k : ℚ)) ^ (m + 1) := by
  have h1 : Qt m S * ∏ k ∈ S, (geom (k : ℚ)) ^ (m + 1) = 1 := by
    rw [Qt_eq]
    have : ∀ T : Finset ℤ, (((∏ k ∈ T, (1 - C (k : ℚ) * X) ^ (m + 1) : ℚ[X])) : PowerSeries ℚ) *
        ∏ k ∈ T, (geom (k : ℚ)) ^ (m + 1) = 1 := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | insert a T ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.coe_mul,
          Polynomial.coe_pow]
        calc _ = ((((1 - C (a : ℚ) * X : ℚ[X])) : PowerSeries ℚ) * geom a) ^ (m + 1) *
              ((((∏ k ∈ T, (1 - C (k : ℚ) * X) ^ (m + 1) : ℚ[X])) : PowerSeries ℚ) *
                ∏ k ∈ T, (geom (k : ℚ)) ^ (m + 1)) := by ring
          _ = 1 := by rw [one_sub_mul_geom, ih, one_pow, one_mul]
    exact this S
  calc Eser m S = Eser m S * (Qt m S * ∏ k ∈ S, (geom (k : ℚ)) ^ (m + 1)) := by rw [h1, mul_one]
    _ = (Eser m S * Qt m S) * ∏ k ∈ S, (geom (k : ℚ)) ^ (m + 1) := by ring
    _ = _ := by rw [Eser_mul_Qt hS, one_mul]

/-- Coefficientwise domination of power series. -/
def Dom (f g : PowerSeries ℚ) : Prop := ∀ k, |PowerSeries.coeff k f| ≤ PowerSeries.coeff k g

lemma Dom.mul {f g f' g' : PowerSeries ℚ} (h : Dom f g) (h' : Dom f' g') : Dom (f * f') (g * g') := by
  intro k
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) ((abs_nonneg _).trans (h _))

lemma Dom.one : Dom 1 1 := by
  intro k; rw [PowerSeries.coeff_one]; split_ifs <;> simp

lemma Dom.pow {f g : PowerSeries ℚ} (h : Dom f g) : ∀ n : ℕ, Dom (f ^ n) (g ^ n)
  | 0 => by simpa using Dom.one
  | n + 1 => by rw [pow_succ, pow_succ]; exact (Dom.pow h n).mul h

lemma Dom.prod {T : Finset ℤ} {f g : ℤ → PowerSeries ℚ} (h : ∀ k ∈ T, Dom (f k) (g k)) :
    Dom (∏ k ∈ T, f k) (∏ k ∈ T, g k) := by
  induction T using Finset.induction_on with
  | empty => simpa using Dom.one
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma Dom_geom {a B : ℚ} (h : |a| ≤ B) : Dom (geom a) (geom B) := by
  intro k
  simp only [geom, PowerSeries.coeff_mk, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) h k

lemma coeff_geom_pow (B : ℚ) (d s : ℕ) :
    PowerSeries.coeff s ((geom B) ^ (d + 1)) = ((d + s).choose d : ℚ) * B ^ s := by
  have : geom B = PowerSeries.rescale B (PowerSeries.mk 1) := by
    rw [PowerSeries.rescale_mk]; simp [geom]
  rw [this, ← map_pow, PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk, mul_comm]

theorem Eser_coeff_bound (hS : S.Nonempty) (B : ℚ) (hB : ∀ k ∈ S, |(k : ℚ)| ≤ B) (s : ℕ) :
    |Lam m S (X ^ ((m + 1) * S.card - 1 + s))| ≤
      (((m + 1) * S.card - 1 + s).choose ((m + 1) * S.card - 1) : ℚ) * B ^ s := by
  have hpos : 0 < (m + 1) * S.card := Nat.mul_pos (Nat.succ_pos m) (Finset.card_pos.2 hS)
  have h1 : Dom (Eser m S) (∏ k ∈ S, (geom B) ^ (m + 1)) := by
    rw [Eser_eq hS]
    exact Dom.prod fun k hk => (Dom_geom (hB k hk)).pow _
  have h2 := h1 s
  simp only [Eser, PowerSeries.coeff_mk] at h2
  rw [Finset.prod_const, ← pow_mul, show (m + 1) * S.card = ((m + 1) * S.card - 1) + 1 by omega,
    coeff_geom_pow] at h2
  simpa using h2

/-- Local coefficients `c h j r = [u^(m-r)] ((j+u)^h P_j(u))`. -/
noncomputable def cc (m : ℕ) (S : Finset ℤ) (h : ℕ) (j : ℤ) (r : ℕ) : ℚ :=
  PowerSeries.coeff (m - r) ((((X + C (j : ℚ)) ^ h : ℚ[X]) : PowerSeries ℚ) * Pj m S j)

/-- Moments `τ h l = ∑_j ∑_{r ≤ m} c h j r · C(l, r) · j^(l-r)`. -/
noncomputable def tau (m : ℕ) (S : Finset ℤ) (h l : ℕ) : ℚ :=
  ∑ j ∈ S, ∑ r ∈ Finset.range (m + 1), cc m S h j r * (l.choose r : ℚ) * (j : ℚ) ^ (l - r)

theorem tau_eq_Lam (h l : ℕ) : tau m S h l = Lam m S (X ^ (l + h)) := by
  unfold tau Lam
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftP_X_pow, pow_add, Polynomial.coe_mul, mul_assoc, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Polynomial.coeff_coe, coeff_X_add_C_pow, cc]
  ring

theorem tau_eq_zero (hS : S.Nonempty) {h l : ℕ} (hl : l + h < (m + 1) * S.card - 1) :
    tau m S h l = 0 := by
  rw [tau_eq_Lam, Lam_X_pow_lt hS hl]

theorem tau_bound (hS : S.Nonempty) (B : ℚ) (hB : ∀ k ∈ S, |(k : ℚ)| ≤ B) {h l : ℕ}
    (hl : (m + 1) * S.card - 1 ≤ l + h) :
    |tau m S h l| ≤ ((l + h).choose ((m + 1) * S.card - 1) : ℚ) *
      B ^ (l + h - ((m + 1) * S.card - 1)) := by
  rw [tau_eq_Lam]
  have := Eser_coeff_bound (m := m) hS B hB (l + h - ((m + 1) * S.card - 1))
  rwa [show (m + 1) * S.card - 1 + (l + h - ((m + 1) * S.card - 1)) = l + h by omega] at this

end PiMahler

end PartAlgebra2

section PartCoeffs

/-!
# Symmetric nodes, integrality and size of the coefficients
-/

namespace PiMahler

open Polynomial

/-- `t ↦ t - n'`. -/
def nodeEmb (n' : ℕ) : ℕ ↪ ℤ := ⟨fun t => (t : ℤ) - n', fun a b h => by simpa using h⟩

/-- The nodes `-n', …, n'`. -/
def nodes (n' : ℕ) : Finset ℤ := (Finset.range (2 * n' + 1)).map (nodeEmb n')

lemma nodeEmb_apply (n' t : ℕ) : nodeEmb n' t = (t : ℤ) - n' := rfl

lemma card_nodes (n' : ℕ) : (nodes n').card = 2 * n' + 1 := by simp [nodes]

lemma nodes_nonempty (n' : ℕ) : (nodes n').Nonempty := by
  rw [← Finset.card_pos, card_nodes]; omega

lemma abs_le_of_mem_nodes {n' : ℕ} {k : ℤ} (hk : k ∈ nodes n') : |(k : ℚ)| ≤ n' := by
  simp only [nodes, Finset.mem_map, Finset.mem_range, nodeEmb_apply] at hk
  obtain ⟨t, ht, rfl⟩ := hk
  push_cast
  rw [abs_le]
  constructor
  · have : (0 : ℚ) ≤ t := by positivity
    linarith
  · have : (t : ℚ) ≤ 2 * n' := by exact_mod_cast (by omega : t ≤ 2 * n')
    linarith

lemma prod_range_sub (i : ℕ) : ∏ t ∈ Finset.range i, ((i : ℚ) - t) = (i.factorial : ℚ) := by
  rw [← Finset.prod_range_reflect]
  rw [Finset.prod_congr rfl (g := fun t => (((t + 1 : ℕ)) : ℚ)), ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]
  intro t ht
  rw [Finset.mem_range] at ht
  rw [show ((i - 1 - t : ℕ) : ℚ) = (i : ℚ) - ((t + 1 : ℕ) : ℚ) by
    rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : i - 1 - t + (t + 1) = i)]
  ring

lemma prod_erase_range (i : ℕ) : ∀ n : ℕ, i ≤ n →
    ∏ t ∈ (Finset.range (n + 1)).erase i, ((i : ℚ) - t) =
      (-1) ^ (n - i) * (i.factorial : ℚ) * ((n - i).factorial : ℚ)
  | 0, h => by
    have : i = 0 := by omega
    subst this; simp
  | n + 1, h => by
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      rw [Finset.range_add_one, Finset.erase_insert (by simp), prod_range_sub]
      simp
    · rw [Finset.range_add_one, Finset.erase_insert_of_ne (by omega),
        Finset.prod_insert (by simp), prod_erase_range i n (by omega)]
      rw [show n + 1 - i = (n - i) + 1 by omega, Nat.factorial_succ, pow_succ]
      push_cast
      rw [Nat.cast_sub (by omega)]
      ring

lemma prod_erase_nodes (n' i : ℕ) (hi : i ≤ 2 * n') :
    ∏ k ∈ (nodes n').erase (nodeEmb n' i), (((nodeEmb n' i : ℤ) : ℚ) - k) =
      (-1) ^ (2 * n' - i) * (i.factorial : ℚ) * ((2 * n' - i).factorial : ℚ) := by
  rw [nodes, ← Finset.map_erase, Finset.prod_map]
  rw [← prod_erase_range i (2 * n') hi]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [nodeEmb_apply]

/-! ### Integrality predicate -/

/-- `D^e · [u^e] f ∈ ℤ` for all `e`. -/
def IntD (D : ℤ) (f : PowerSeries ℚ) : Prop := ∀ e, ∃ z : ℤ, (D : ℚ) ^ e * PowerSeries.coeff e f = z

lemma IntD.mul {D : ℤ} {f g : PowerSeries ℚ} (hf : IntD D f) (hg : IntD D g) : IntD D (f * g) := by
  choose zf hzf using hf
  choose zg hzg using hg
  intro e
  refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal e, zf p.1 * zg p.2, ?_⟩
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← hzf, ← hzg, ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hp), pow_add]
  ring

lemma IntD.one (D : ℤ) : IntD D 1 := by
  intro e
  refine ⟨if e = 0 then 1 else 0, ?_⟩
  rw [PowerSeries.coeff_one]
  split_ifs with h <;> simp [h]

lemma IntD.pow {D : ℤ} {f : PowerSeries ℚ} (hf : IntD D f) : ∀ n : ℕ, IntD D (f ^ n)
  | 0 => by simpa using IntD.one D
  | n + 1 => by rw [pow_succ]; exact (IntD.pow hf n).mul hf

lemma IntD.prod {D : ℤ} {T : Finset ℤ} {f : ℤ → PowerSeries ℚ} (h : ∀ k ∈ T, IntD D (f k)) :
    IntD D (∏ k ∈ T, f k) := by
  induction T using Finset.induction_on with
  | empty => simpa using IntD.one D
  | insert a T ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma IntD.intPoly (D : ℤ) (p : ℤ[X]) : IntD D ((p.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) := by
  intro e
  refine ⟨D ^ e * p.coeff e, ?_⟩
  rw [Polynomial.coeff_coe, coeff_map]
  push_cast; rfl

/-- `1/(1 + u/a)` -/
noncomputable def invN (a : ℚ) : PowerSeries ℚ := PowerSeries.mk fun e => (-1) ^ e / a ^ e

lemma invLin_eq (a : ℚ) : invLin a = PowerSeries.C (a⁻¹) * invN a := by
  ext e
  simp only [invLin, invN, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
  rw [pow_succ]; field_simp

lemma IntD_invN {D a : ℤ} (ha : a ≠ 0) (hD : a ∣ D) : IntD D (invN (a : ℚ)) := by
  obtain ⟨c, rfl⟩ := hD
  intro e
  refine ⟨(-1) ^ e * c ^ e, ?_⟩
  simp only [invN, PowerSeries.coeff_mk]
  have : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  push_cast
  field_simp
  ring

/-! ### The coefficients `a h j s` -/

variable (m n' : ℕ)

/-- `a h j s = c h j s / s!`. -/
noncomputable def aa (h : ℕ) (j : ℤ) (s : ℕ) : ℚ := cc m (nodes n') h j s / (s.factorial : ℚ)

/-- The normalising integer `K = (n!)^(m+1) · D^m · m!`, `n = 2n'`, `D = lcm(1..n)`. -/
def Knorm : ℕ := (2 * n').factorial ^ (m + 1) * (lcmUpTo (2 * n')) ^ m * m.factorial

/-- `∏_{k ≠ j} (j-k + u)^{-(m+1)}` with the constant factor removed. -/
noncomputable def PN (j : ℤ) : PowerSeries ℚ := ∏ k ∈ (nodes n').erase j, (invN ((j : ℚ) - k)) ^ (m + 1)

lemma Pj_eq (j : ℤ) : Pj m (nodes n') j =
    PowerSeries.C ((∏ k ∈ (nodes n').erase j, ((j : ℚ) - k))⁻¹ ^ (m + 1)) * PN m n' j := by
  unfold Pj PN
  simp_rw [invLin_eq, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, ← Finset.prod_inv_distrib,
    Finset.prod_pow]

lemma cc_eq (h : ℕ) (j : ℤ) (s : ℕ) : cc m (nodes n') h j s =
    (∏ k ∈ (nodes n').erase j, ((j : ℚ) - k))⁻¹ ^ (m + 1) *
      PowerSeries.coeff (m - s) ((((X + C (j : ℚ)) ^ h : ℚ[X]) : PowerSeries ℚ) * PN m n' j) := by
  unfold cc
  rw [Pj_eq, mul_left_comm, PowerSeries.coeff_C_mul]

lemma IntD_PN (j : ℤ) (hj : j ∈ nodes n') : IntD (lcmUpTo (2 * n')) (PN m n' j) := by
  unfold PN
  apply IntD.prod
  intro k hk
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  have hk' : k ∈ nodes n' := Finset.mem_of_mem_erase hk
  have hne : j - k ≠ 0 := sub_ne_zero.2 (Ne.symm hkj)
  have hdvd : j - k ∣ (lcmUpTo (2 * n') : ℤ) := by
    rw [← Int.natAbs_dvd]
    apply Int.natCast_dvd_natCast.2
    apply dvd_lcmUpTo
    · exact Int.natAbs_pos.2 hne
    · have h1 := abs_le_of_mem_nodes hj
      have h2 := abs_le_of_mem_nodes hk'
      have h1' : |j| ≤ (n' : ℤ) := by exact_mod_cast h1
      have h2' : |k| ≤ (n' : ℤ) := by exact_mod_cast h2
      rw [abs_le] at h1' h2'
      omega
  have := IntD_invN hne hdvd
  push_cast at this
  exact this.pow _

lemma IntD_shiftPoly (D : ℤ) (h : ℕ) (j : ℤ) :
    IntD D ((((X + C (j : ℚ)) ^ h : ℚ[X])) : PowerSeries ℚ) := by
  have := IntD.intPoly D ((X + C j) ^ h)
  simpa [Polynomial.map_pow] using this

theorem aa_int (h s : ℕ) (hs : s ≤ m) (i : ℕ) (hi : i ≤ 2 * n') :
    ∃ z : ℤ, (Knorm m n' : ℚ) * aa m n' h (nodeEmb n' i) s = z := by
  set j := nodeEmb n' i with hjdef
  have hj : j ∈ nodes n' := Finset.mem_map_of_mem _ (Finset.mem_range.2 (by omega))
  set D : ℕ := lcmUpTo (2 * n') with hD
  obtain ⟨w, hw⟩ := (IntD_shiftPoly (D : ℤ) h j).mul (IntD_PN m n' j hj) (m - s)
  have hprod := prod_erase_nodes n' i hi
  rw [← hjdef] at hprod
  have hfac : (i.factorial * (2 * n' - i).factorial) ∣ (2 * n').factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add i (2 * n' - i)
    rwa [Nat.add_sub_cancel' hi] at this
  obtain ⟨b, hb⟩ := hfac
  have hsf : s.factorial ∣ m.factorial := Nat.factorial_dvd_factorial hs
  obtain ⟨c, hc⟩ := hsf
  refine ⟨(-1) ^ ((2 * n' - i) * (m + 1)) * b ^ (m + 1) * D ^ s * c * w, ?_⟩
  unfold aa Knorm
  rw [cc_eq, hprod]
  set W := PowerSeries.coeff (m - s) ((((X + C (j : ℚ)) ^ h : ℚ[X]) : PowerSeries ℚ) * PN m n' j)
    with hWdef
  set σ : ℚ := (-1) ^ (2 * n' - i) with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ, ← pow_add, ← two_mul, pow_mul]; simp
  have hσinv : σ⁻¹ = σ := by
    exact inv_eq_of_mul_eq_one_right hσ2
  have hinv : (σ * (i.factorial : ℚ) * ((2 * n' - i).factorial : ℚ))⁻¹ ^ (m + 1) =
      σ ^ (m + 1) * (((i.factorial : ℚ) * ((2 * n' - i).factorial : ℚ)) ^ (m + 1))⁻¹ := by
    rw [mul_assoc, mul_inv, hσinv, mul_pow, inv_pow]
  rw [hinv]
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast (lcmUpTo_pos _).ne'
  have hi0 : (i.factorial : ℚ) ≠ 0 := by positivity
  have hi1 : ((2 * n' - i).factorial : ℚ) ≠ 0 := by positivity
  have hs0 : (s.factorial : ℚ) ≠ 0 := by positivity
  have hpow : (D : ℚ) ^ m = (D : ℚ) ^ s * (D : ℚ) ^ (m - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hs]
  have hw' : ((D : ℤ) : ℚ) ^ (m - s) = (D : ℚ) ^ (m - s) := by push_cast; rfl
  rw [hw'] at hw
  push_cast
  rw [hb, hc, hpow, pow_mul, ← hσ]
  push_cast
  rw [← hw]
  field_simp
  ring

/-! ### Size bounds -/

lemma Dom_invN {a : ℚ} (ha : 1 ≤ |a|) : Dom (invN a) (geom 1) := by
  intro e
  simp only [invN, geom, PowerSeries.coeff_mk, one_pow, abs_div, abs_pow, abs_neg, abs_one]
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ ha

lemma Dom_shiftPoly (h : ℕ) (j : ℤ) (hj : |(j : ℚ)| ≤ n') :
    Dom ((((X + C (j : ℚ)) ^ h : ℚ[X])) : PowerSeries ℚ)
      (PowerSeries.C (((n' : ℚ) + 1) ^ h) * geom 1) := by
  intro e
  rw [Polynomial.coeff_coe, coeff_X_add_C_pow, PowerSeries.coeff_C_mul]
  simp only [geom, PowerSeries.coeff_mk, one_pow, mul_one]
  rw [abs_mul, abs_pow, Nat.abs_cast]
  have h1 : |(j : ℚ)| ^ (h - e) ≤ (n' : ℚ) ^ (h - e) := pow_le_pow_left₀ (abs_nonneg _) hj _
  have h2 : ((n' : ℚ)) ^ (h - e) * (h.choose e : ℚ) ≤ ((n' : ℚ) + 1) ^ h := by
    rcases Nat.lt_or_ge h e with he | he
    · rw [Nat.choose_eq_zero_of_lt he]; simp; positivity
    · have := choose_mul_pow_le_add_pow h e 1 n' he
      have : ((h.choose e * (1 ^ e * n' ^ (h - e)) : ℕ) : ℚ) ≤ ((1 + n') ^ h : ℕ) := by
        exact_mod_cast this
      push_cast at this
      calc ((n' : ℚ)) ^ (h - e) * (h.choose e : ℚ) = (h.choose e : ℚ) * (1 ^ e * (n' : ℚ) ^ (h - e)) := by
            ring
        _ ≤ (1 + (n' : ℚ)) ^ h := this
        _ = _ := by ring
  calc |(j : ℚ)| ^ (h - e) * (h.choose e : ℚ) ≤ (n' : ℚ) ^ (h - e) * (h.choose e : ℚ) := by
        gcongr
    _ ≤ _ := h2

lemma coeff_bound_w (h : ℕ) (j : ℤ) (hj : j ∈ nodes n') (e : ℕ) :
    |PowerSeries.coeff e ((((X + C (j : ℚ)) ^ h : ℚ[X]) : PowerSeries ℚ) * PN m n' j)| ≤
      ((n' : ℚ) + 1) ^ h * (((m + 1) * (2 * n') + e).choose ((m + 1) * (2 * n')) : ℚ) := by
  have hD : Dom (PN m n' j) (∏ k ∈ (nodes n').erase j, (geom 1) ^ (m + 1)) := by
    unfold PN
    apply Dom.prod
    intro k hk
    apply Dom.pow
    apply Dom_invN
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have : (1 : ℤ) ≤ |j - k| := Int.one_le_abs (sub_ne_zero.2 (Ne.symm hkj))
    have : (1 : ℚ) ≤ |((j - k : ℤ) : ℚ)| := by exact_mod_cast this
    push_cast at this; exact this
  have h2 := (Dom_shiftPoly n' h j (abs_le_of_mem_nodes hj)).mul hD e
  rw [Finset.prod_const, Finset.card_erase_of_mem hj, card_nodes, Nat.add_sub_cancel,
    ← pow_mul] at h2
  rw [mul_assoc, ← pow_succ', PowerSeries.coeff_C_mul, coeff_geom_pow, one_pow, mul_one] at h2
  exact h2

theorem aa_bound (h s : ℕ) (hs : s ≤ m) (hh : h ≤ m) (i : ℕ) (hi : i ≤ 2 * n') :
    |(Knorm m n' : ℚ) * aa m n' h (nodeEmb n' i) s| ≤
      ((2 * n').choose i : ℚ) ^ (m + 1) * (lcmUpTo (2 * n') : ℚ) ^ m * (m.factorial : ℚ) *
        ((n' : ℚ) + 1) ^ m * (((m + 1) * (2 * n') + m).choose ((m + 1) * (2 * n')) : ℚ) := by
  set j := nodeEmb n' i with hjdef
  have hj : j ∈ nodes n' := Finset.mem_map_of_mem _ (Finset.mem_range.2 (by omega))
  have hprod := prod_erase_nodes n' i hi
  rw [← hjdef] at hprod
  have hw := coeff_bound_w m n' h j hj (m - s)
  have hfac : (i.factorial * (2 * n' - i).factorial : ℚ) * ((2 * n').choose i : ℚ) =
      ((2 * n').factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial hi
    rw [← this]; push_cast; ring
  unfold aa Knorm
  rw [cc_eq, hprod]
  set W := PowerSeries.coeff (m - s) ((((X + C (j : ℚ)) ^ h : ℚ[X]) : PowerSeries ℚ) * PN m n' j)
  have hi0 : (i.factorial : ℚ) ≠ 0 := by positivity
  have hi1 : ((2 * n' - i).factorial : ℚ) ≠ 0 := by positivity
  have hs0 : (s.factorial : ℚ) ≠ 0 := by positivity
  have hD1 : (1 : ℚ) ≤ (lcmUpTo (2 * n') : ℚ) := by exact_mod_cast lcmUpTo_pos _
  set σ : ℚ := (-1) ^ (2 * n' - i) with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ, ← pow_add, ← two_mul, pow_mul]; simp
  have hσinv : σ⁻¹ = σ := by
    exact inv_eq_of_mul_eq_one_right hσ2
  have hinv : (σ * (i.factorial : ℚ) * ((2 * n' - i).factorial : ℚ))⁻¹ ^ (m + 1) =
      σ ^ (m + 1) * (((i.factorial : ℚ) * ((2 * n' - i).factorial : ℚ)) ^ (m + 1))⁻¹ := by
    rw [mul_assoc, mul_inv, hσinv, mul_pow, inv_pow]
  have key : (((2 * n').factorial ^ (m + 1) * lcmUpTo (2 * n') ^ m * m.factorial : ℕ) : ℚ) *
      ((σ * (i.factorial : ℚ) * ((2 * n' - i).factorial : ℚ))⁻¹ ^ (m + 1) * W /
        (s.factorial : ℚ)) =
      σ ^ (m + 1) * ((2 * n').choose i : ℚ) ^ (m + 1) *
        (lcmUpTo (2 * n') : ℚ) ^ m * ((m.factorial : ℚ) / s.factorial) * W := by
    rw [hinv]
    push_cast
    rw [← hfac]
    field_simp
    ring
  rw [key, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, hσ, abs_pow, abs_neg, abs_one, one_pow,
    one_pow, one_mul]
  have hW : |W| ≤ ((n' : ℚ) + 1) ^ m *
      (((m + 1) * (2 * n') + m).choose ((m + 1) * (2 * n')) : ℚ) := by
    refine hw.trans (mul_le_mul (pow_le_pow_right₀ (by linarith) hh)
      (by exact_mod_cast Nat.choose_le_choose _ (by omega)) (by positivity) (by positivity))
  have hmf : |(m.factorial : ℚ) / s.factorial| ≤ m.factorial := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : (1 : ℚ) ≤ s.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero s)
    nlinarith [show (0 : ℚ) ≤ m.factorial by positivity]
  rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((2 * n').choose i : ℚ) ^ (m + 1)),
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ (lcmUpTo (2 * n') : ℚ) ^ m)]
  calc ((2 * n').choose i : ℚ) ^ (m + 1) * (lcmUpTo (2 * n') : ℚ) ^ m *
        |(m.factorial : ℚ) / s.factorial| * |W|
      ≤ ((2 * n').choose i : ℚ) ^ (m + 1) * (lcmUpTo (2 * n') : ℚ) ^ m *
        (m.factorial : ℚ) * (((n' : ℚ) + 1) ^ m *
          (((m + 1) * (2 * n') + m).choose ((m + 1) * (2 * n')) : ℚ)) := by
        gcongr
    _ = _ := by ring

end PiMahler

end PartCoeffs

section PartDet

/-!
# Non-vanishing of the determinant

For every complex `y₀` some auxiliary polynomial `S_h(Y) = ∑_s (∑_i a h (i-n') s · I^i) Y^s`
does not vanish at `y₀`.
-/

namespace PiMahler

open Polynomial Matrix

variable (m n' : ℕ)

lemma coe_finset_sum_ps {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    ((∑ i ∈ s, f i : ℚ[X]) : PowerSeries ℚ) = ∑ i ∈ s, (f i : PowerSeries ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Polynomial.coe_add, ih, Finset.sum_insert ha]

lemma sum_aa_eq_tau (h L : ℕ) :
    ∑ j ∈ nodes n', ∑ s ∈ Finset.range (m + 1), aa m n' h j s *
        (if s ≤ L then (j : ℚ) ^ (L - s) / ((L - s).factorial : ℚ) else 0) =
      tau m (nodes n') h L / (L.factorial : ℚ) := by
  unfold tau aa
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · have := Nat.choose_mul_factorial_mul_factorial hs
    have hL : (L.factorial : ℚ) = (L.choose s : ℚ) * s.factorial * (L - s).factorial := by
      rw [← this]; push_cast; ring
    rw [hL]
    have h1 : (s.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((L - s).factorial : ℚ) ≠ 0 := by positivity
    have h3 : (L.choose s : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hs).ne'
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The polynomial matrix `P_{hs}(x) = ∑_i a h (i - n') s x^i`. -/
noncomputable def Pmat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ[X] :=
  fun h s => ∑ i ∈ Finset.range (2 * n' + 1), C (aa m n' h (nodeEmb n' i) s) * X ^ i

lemma natDegree_Pmat_le (h s : Fin (m + 1)) : (Pmat m n' h s).natDegree ≤ 2 * n' := by
  unfold Pmat
  apply natDegree_sum_le_of_forall_le
  intro i hi
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)

lemma natDegree_det_Pmat_le : (Pmat m n').det.natDegree ≤ (m + 1) * (2 * n') := by
  rw [Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_mul_le).trans ?_
  have h1 : ((((Equiv.Perm.sign σ : ℤ)) : ℚ[X])).natDegree = 0 := natDegree_intCast _
  rw [h1, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (Pmat m n' (σ i) i).natDegree ≤ ∑ _i : Fin (m + 1), 2 * n' :=
        Finset.sum_le_sum fun i _ => natDegree_Pmat_le m n' _ _
    _ = (m + 1) * (2 * n') := by simp

lemma eval_zero_Pmat (h s : Fin (m + 1)) :
    (Pmat m n' h s).eval 0 = aa m n' h (nodeEmb n' 0) s := by
  unfold Pmat
  rw [eval_finset_sum, Finset.sum_range_succ']
  simp

lemma eval_zero_det_ne : (Pmat m n').det.eval 0 ≠ 0 := by
  rw [← coe_evalRingHom, RingHom.map_det]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  apply hv0
  set j := nodeEmb n' 0 with hj
  have hjS : j ∈ nodes n' := Finset.mem_map_of_mem _ (Finset.mem_range.2 (by omega))
  -- the linear relation between the rows
  have hrel : ∀ s : Fin (m + 1), ∑ h : Fin (m + 1), v h * cc m (nodes n') h j s = 0 := by
    intro s
    have := congrFun hv s
    simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_evalRingHom, eval_zero_Pmat, Pi.zero_apply] at this
    unfold aa at this
    have hs0 : (((s : ℕ).factorial : ℚ)) ≠ 0 := by positivity
    have : (∑ h : Fin (m + 1), v h * cc m (nodes n') h j s) / ((s : ℕ).factorial : ℚ) = 0 := by
      rw [← this, Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rwa [div_eq_zero_iff, or_iff_left hs0] at this
  set V : ℚ[X] := ∑ h : Fin (m + 1), C (v h) * (X + C (j : ℚ)) ^ (h : ℕ) with hV
  have hVcoeff : ∀ e ≤ m,
      PowerSeries.coeff e (((V : ℚ[X]) : PowerSeries ℚ) * Pj m (nodes n') j) = 0 := by
    intro e he
    have := hrel ⟨m - e, by omega⟩
    simp only [cc, show m - (m - e) = e by omega] at this
    rw [← this, hV]
    rw [show (((∑ h : Fin (m + 1), C (v h) * (X + C (j : ℚ)) ^ (h : ℕ) : ℚ[X])) :
        PowerSeries ℚ) * Pj m (nodes n') j = ∑ h : Fin (m + 1), PowerSeries.C (v h) *
          ((((X + C (j : ℚ)) ^ (h : ℕ) : ℚ[X]) : PowerSeries ℚ) * Pj m (nodes n') j) by
      rw [show (((∑ h : Fin (m + 1), C (v h) * (X + C (j : ℚ)) ^ (h : ℕ) : ℚ[X])) :
          PowerSeries ℚ) = ∑ h : Fin (m + 1), (((C (v h) * (X + C (j : ℚ)) ^ (h : ℕ) : ℚ[X])) :
            PowerSeries ℚ) from coe_finset_sum_ps _ _]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Polynomial.coe_mul, Polynomial.coe_C, mul_assoc]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [PowerSeries.coeff_C_mul]
  -- hence the low coefficients of `V` vanish
  have hVlow : ∀ e ≤ m, V.coeff e = 0 := by
    intro e he
    have h1 : ((V : ℚ[X]) : PowerSeries ℚ) = (((V : ℚ[X]) : PowerSeries ℚ) * Pj m (nodes n') j) *
        ((shiftP j (Qj m (nodes n') j) : ℚ[X]) : PowerSeries ℚ) := by
      rw [mul_assoc, mul_comm (Pj m (nodes n') j), shift_Qj_mul_Pj, mul_one]
    rw [← Polynomial.coeff_coe, h1, mul_comm, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [hVcoeff p.2 (by omega), mul_zero]
  have hVdeg : V.natDegree ≤ m := by
    rw [hV]
    apply natDegree_sum_le_of_forall_le
    intro h _
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_pow_le).trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact Nat.lt_succ_iff.1 h.2
  have hV0 : V = 0 := by
    ext e
    rw [coeff_zero]
    rcases Nat.lt_or_ge m e with h | h
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hVdeg h)
    · exact hVlow e h
  have hV1 : V.comp (X - C (j : ℚ)) = ∑ h : Fin (m + 1), C (v h) * X ^ (h : ℕ) := by
    rw [hV]
    simp [sum_comp, mul_comp, pow_comp]
  rw [hV0, zero_comp] at hV1
  funext h
  have := congrArg (fun P => P.coeff h) hV1
  simp only [coeff_zero, finset_sum_coeff, coeff_C_mul, coeff_X_pow] at this
  rw [Finset.sum_eq_single h (fun b _ hb => by
    rw [if_neg (fun e => hb (Fin.ext e.symm)), mul_zero]) (by simp)] at this
  simpa using this.symm

/-! ### Power series argument -/

open PowerSeries in
lemma coeff_X_pow_mul_rescale_exp (s L : ℕ) (a : ℚ) :
    coeff L ((X : PowerSeries ℚ) ^ s * rescale a (exp ℚ)) =
      if s ≤ L then a ^ (L - s) / ((L - s).factorial : ℚ) else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs
  · rw [coeff_rescale, coeff_exp]; simp [div_eq_mul_inv]
  · rfl

lemma X_pow_dvd_Rj (h : Fin (m + 1)) :
    (PowerSeries.X : PowerSeries ℚ) ^ ((m + 1) * (2 * n')) ∣
      ∑ s : Fin (m + 1), ∑ i ∈ Finset.range (2 * n' + 1),
        PowerSeries.C (aa m n' h (nodeEmb n' i) s) *
          ((PowerSeries.X : PowerSeries ℚ) ^ (s : ℕ) *
            PowerSeries.rescale (((nodeEmb n' i : ℤ) : ℚ)) (PowerSeries.exp ℚ)) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro L hL
  simp only [map_sum, PowerSeries.coeff_C_mul, coeff_X_pow_mul_rescale_exp]
  rw [Finset.sum_comm]
  have e1 : ∀ i, ∑ s : Fin (m + 1), aa m n' h (nodeEmb n' i) s *
      (if (s : ℕ) ≤ L then (((nodeEmb n' i : ℤ) : ℚ)) ^ (L - s) / ((L - s).factorial : ℚ) else 0) =
      ∑ s ∈ Finset.range (m + 1), aa m n' h (nodeEmb n' i) s *
      (if s ≤ L then (((nodeEmb n' i : ℤ) : ℚ)) ^ (L - s) / ((L - s).factorial : ℚ) else 0) :=
    fun i => Fin.sum_univ_eq_sum_range (fun s => aa m n' h (nodeEmb n' i) s *
      (if s ≤ L then (((nodeEmb n' i : ℤ) : ℚ)) ^ (L - s) / ((L - s).factorial : ℚ) else 0)) (m + 1)
  rw [Finset.sum_congr rfl (fun i _ => e1 i)]
  have := sum_aa_eq_tau m n' h L
  rw [nodes, Finset.sum_map] at this
  rw [this, ← nodes, tau_eq_zero (nodes_nonempty n') (by
    rw [card_nodes, Nat.mul_succ]; have := h.2; omega), zero_div]

lemma X_pow_dvd_aeval_det :
    (PowerSeries.X : PowerSeries ℚ) ^ ((m + 1) * (2 * n')) ∣
      Polynomial.aeval (PowerSeries.exp ℚ) (Pmat m n').det := by
  set Mps := (Polynomial.aeval (PowerSeries.exp ℚ)).toRingHom.mapMatrix (Pmat m n') with hMps
  have hdet : Polynomial.aeval (PowerSeries.exp ℚ) (Pmat m n').det = Mps.det := by
    rw [hMps, ← RingHom.map_det]; rfl
  rw [hdet]
  set w : Fin (m + 1) → PowerSeries ℚ := fun s => PowerSeries.X ^ (s : ℕ) with hw
  have hrow : ∀ h, (PowerSeries.X : PowerSeries ℚ) ^ ((m + 1) * (2 * n')) ∣ (Mps *ᵥ w) h := by
    intro h
    have hfac : (Mps *ᵥ w) h = PowerSeries.rescale (n' : ℚ) (PowerSeries.exp ℚ) *
        ∑ s : Fin (m + 1), ∑ i ∈ Finset.range (2 * n' + 1),
          PowerSeries.C (aa m n' h (nodeEmb n' i) s) *
            ((PowerSeries.X : PowerSeries ℚ) ^ (s : ℕ) *
              PowerSeries.rescale (((nodeEmb n' i : ℤ) : ℚ)) (PowerSeries.exp ℚ)) := by
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hMps, RingHom.mapMatrix_apply, Matrix.map_apply, hw]
      simp only [Pmat, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [Finset.mul_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, aeval_C, map_pow, aeval_X, PowerSeries.exp_pow_eq_rescale_exp]
      have : PowerSeries.rescale ((i : ℕ) : ℚ) (PowerSeries.exp ℚ) =
          PowerSeries.rescale (n' : ℚ) (PowerSeries.exp ℚ) *
            PowerSeries.rescale (((nodeEmb n' i : ℤ) : ℚ)) (PowerSeries.exp ℚ) := by
        rw [PowerSeries.exp_mul_exp_eq_exp_add]; congr 1; simp [nodeEmb_apply]
      rw [this, PowerSeries.algebraMap_eq]
      ring
    rw [hfac]
    exact Dvd.dvd.mul_left (X_pow_dvd_Rj m n' h) _
  have hadj : Mps.det • w = Mps.adjugate *ᵥ (Mps *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h0 := congrFun hadj 0
  simp only [Pi.smul_apply, hw, Fin.val_zero, pow_zero, smul_eq_mul, mul_one] at h0
  rw [h0, Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun h _ => Dvd.dvd.mul_left (hrow h) _

/-- A polynomial of degree `≤ d` with `X^d ∣ D(e^y)` is a multiple of `(x-1)^d`. -/
lemma aeval_ne_zero_of_X_pow_dvd (D : ℚ[X]) (d : ℕ) (hdeg : D.natDegree ≤ d)
    (hdvd : (PowerSeries.X : PowerSeries ℚ) ^ d ∣ Polynomial.aeval (PowerSeries.exp ℚ) D)
    (h0 : D.eval 0 ≠ 0) (z : ℂ) (hz : z ≠ 1) : Polynomial.aeval z D ≠ 0 := by
  set G := D.comp (X + 1) with hG
  have hDG : D = G.comp (X - 1) := by
    rw [hG, comp_assoc]; simp
  set U : PowerSeries ℚ := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (PowerSeries.exp ℚ)
    with hU
  have hXU : Polynomial.aeval (PowerSeries.exp ℚ) (X - 1 : ℚ[X]) = PowerSeries.X * U := by
    rw [map_sub, aeval_X, map_one]
    ext k
    rcases k with _ | k
    · simp
    · rw [map_sub, PowerSeries.coeff_succ_X_mul, hU, PowerSeries.coeff_mk, PowerSeries.coeff_one]
      simp
  have hU0 : PowerSeries.constantCoeff U = 1 := by
    rw [hU, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simp [PowerSeries.coeff_exp]
  have hE : Polynomial.aeval (PowerSeries.exp ℚ) D = Polynomial.aeval (PowerSeries.X * U) G := by
    conv_lhs => rw [hDG]
    rw [aeval_comp, hXU]
  -- all coefficients of `G` below `d` vanish
  have hlow : ∀ k < d, G.coeff k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    have hc : PowerSeries.coeff k (Polynomial.aeval (PowerSeries.X * U) G) = 0 := by
      rw [← hE]
      exact (PowerSeries.X_pow_dvd_iff.1 hdvd) k hk
    rw [aeval_eq_sum_range' (n := max (G.natDegree + 1) (k + 1)) (by omega), map_sum] at hc
    rw [Finset.sum_eq_single k] at hc
    · rw [PowerSeries.coeff_smul, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl,
        Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hU0, one_pow,
        smul_eq_mul, mul_one] at hc
      exact hc
    · intro b _ hb
      rcases Nat.lt_or_gt_of_ne hb with hb | hb
      · rw [ih b hb (by omega), zero_smul, map_zero]
      · rw [PowerSeries.coeff_smul, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega),
          smul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hGdeg : G.natDegree ≤ d := by
    rw [hG, natDegree_comp, ← C_1, natDegree_X_add_C, mul_one]; exact hdeg
  have hGeq : G = C (G.coeff d) * X ^ d := by
    ext k
    rw [coeff_C_mul, coeff_X_pow]
    rcases lt_trichotomy k d with h | h | h
    · rw [hlow k h, if_neg (by omega), mul_zero]
    · subst h; simp
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega), mul_zero]
  have hDeq : D = C (G.coeff d) * (X - 1) ^ d := by
    rw [hDG, hGeq]; simp [mul_comp]
  have hg : G.coeff d ≠ 0 := by
    intro hg; apply h0; rw [hDeq, hg]; simp
  rw [hDeq, map_mul, aeval_C, map_pow, map_sub, aeval_X, map_one]
  exact mul_ne_zero (by simpa using hg) (pow_ne_zero _ (sub_ne_zero.2 hz))

/-- **Non-vanishing.** For every `y₀ : ℂ` some `S_h(y₀) ≠ 0`. -/
theorem exists_S_ne_zero (y0 : ℂ) : ∃ h : Fin (m + 1),
    ∑ s : Fin (m + 1), (∑ i ∈ Finset.range (2 * n' + 1),
      ((aa m n' h (nodeEmb n' i) s : ℚ) : ℂ) * Complex.I ^ i) * y0 ^ (s : ℕ) ≠ 0 := by
  have hD : Polynomial.aeval Complex.I (Pmat m n').det ≠ 0 :=
    aeval_ne_zero_of_X_pow_dvd _ _ (natDegree_det_Pmat_le m n') (X_pow_dvd_aeval_det m n')
      (eval_zero_det_ne m n') Complex.I (by
        intro h; have := congrArg Complex.re h; simp at this)
  set Mc := (Polynomial.aeval Complex.I).toRingHom.mapMatrix (Pmat m n') with hMc
  have hdet : Mc.det ≠ 0 := by
    rw [hMc, ← RingHom.map_det]; exact hD
  by_contra hcon
  push_neg at hcon
  set v : Fin (m + 1) → ℂ := fun s => y0 ^ (s : ℕ) with hv
  have hMv : Mc *ᵥ v = 0 := by
    funext h
    rw [Pi.zero_apply, ← hcon h]
    simp only [Matrix.mulVec, dotProduct, hMc, RingHom.mapMatrix_apply, Matrix.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hv, Pmat]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X]
    rfl
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hMv
  have h0 := congrFun this 0
  simp [hv] at h0

end PiMahler

end PartDet

section PartAnalytic

/-!
# Analytic bound for the remainder

`R_h(y) = ∑_j ∑_s a h j s · y^s · e^{j y}` is small for small `y`.
-/

namespace PiMahler

variable (m n' : ℕ)

lemma pow_div_factorial_le {r : ℝ} (hr : 0 ≤ r) (a : ℕ) :
    ∀ b : ℕ, r ^ (a + b) / ((a + b).factorial : ℝ) ≤
      r ^ a / (a.factorial : ℝ) * (r / (a + 1)) ^ b
  | 0 => by simp
  | b + 1 => by
    have ih := pow_div_factorial_le hr a b
    rw [show a + (b + 1) = (a + b) + 1 by ring, pow_succ, Nat.factorial_succ, pow_succ]
    push_cast
    have h1 : r ^ (a + b) * r / (((a + b : ℝ) + 1) * ((a + b).factorial : ℝ)) =
        r ^ (a + b) / ((a + b).factorial : ℝ) * (r / ((a + b : ℝ) + 1)) := by
      field_simp
    rw [h1, ← mul_assoc]
    apply mul_le_mul ih _ (by positivity) (by positivity)
    apply div_le_div_of_nonneg_left hr (by positivity)
    have : (a : ℝ) ≤ a + b := by have := (Nat.cast_nonneg (α := ℝ) b); linarith
    linarith

lemma exp_shift_hasSum (s : ℕ) (a y : ℂ) :
    HasSum (fun L : ℕ => if s ≤ L then a ^ (L - s) / ((L - s).factorial : ℂ) * y ^ L else 0)
      (y ^ s * Complex.exp (a * y)) := by
  rw [← hasSum_nat_add_iff' s]
  have hz : ∑ i ∈ Finset.range s,
      (if s ≤ i then a ^ (i - s) / ((i - s).factorial : ℂ) * y ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by simpa using hi)]
  rw [hz, sub_zero]
  have h := (NormedSpace.expSeries_div_hasSum_exp (a * y)).mul_left (y ^ s)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have e : (fun t : ℕ => if s ≤ t + s then a ^ (t + s - s) / ((t + s - s).factorial : ℂ) *
      y ^ (t + s) else 0) = fun t => y ^ s * ((a * y) ^ t / (t.factorial : ℂ)) := by
    funext t
    rw [if_pos (by omega), Nat.add_sub_cancel, pow_add, mul_pow]
    ring
  rw [e]
  exact h

/-- The coefficient of `y^L` in `R_h`. -/
lemma coeff_R_eq (h L : ℕ) (y : ℂ) :
    ∑ i ∈ Finset.range (2 * n' + 1), ∑ s ∈ Finset.range (m + 1),
      (aa m n' h (nodeEmb n' i) s : ℂ) *
        (if s ≤ L then (((nodeEmb n' i : ℤ) : ℂ)) ^ (L - s) / ((L - s).factorial : ℂ) * y ^ L
          else 0) =
      ((tau m (nodes n') h L / (L.factorial : ℚ) : ℚ) : ℂ) * y ^ L := by
  have := sum_aa_eq_tau m n' h L
  conv_lhs at this => rw [nodes, Finset.sum_map]
  rw [← this]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp; ring

lemma R_hasSum (h : ℕ) (y : ℂ) :
    HasSum (fun L : ℕ => ((tau m (nodes n') h L / (L.factorial : ℚ) : ℚ) : ℂ) * y ^ L)
      (∑ i ∈ Finset.range (2 * n' + 1), ∑ s ∈ Finset.range (m + 1),
        (aa m n' h (nodeEmb n' i) s : ℂ) *
          (y ^ s * Complex.exp (((nodeEmb n' i : ℤ) : ℂ) * y))) := by
  have : (fun L : ℕ => ((tau m (nodes n') h L / (L.factorial : ℚ) : ℚ) : ℂ) * y ^ L) =
      fun L => ∑ i ∈ Finset.range (2 * n' + 1), ∑ s ∈ Finset.range (m + 1),
      (aa m n' h (nodeEmb n' i) s : ℂ) *
        (if s ≤ L then (((nodeEmb n' i : ℤ) : ℂ)) ^ (L - s) / ((L - s).factorial : ℂ) * y ^ L
          else 0) := by
    funext L; rw [coeff_R_eq]
  rw [this]
  apply hasSum_sum
  intro i _
  apply hasSum_sum
  intro s _
  exact (exp_shift_hasSum s _ y).mul_left _

/-- **Analytic bound.** For `‖y‖ ≤ r`, with `M₀ = (m+1)·2n'`, `N = M₀ + m` and
`z = n' r / (M₀ + 1) < 1`, `|R_h(y)| ≤ r^M₀ / M₀! · (1 - z)^{-(N+1)}`. -/
theorem R_bound (h : ℕ) (hh : h ≤ m) (y : ℂ) (r : ℝ) (hy : ‖y‖ ≤ r)
    (hr : r ≤ ((m + 1) * (2 * n') : ℕ) + 1)
    (hz : (n' : ℝ) * r / (((m + 1) * (2 * n') : ℕ) + 1) < 1) :
    ‖∑ i ∈ Finset.range (2 * n' + 1), ∑ s ∈ Finset.range (m + 1),
        (aa m n' h (nodeEmb n' i) s : ℂ) *
          (y ^ s * Complex.exp (((nodeEmb n' i : ℤ) : ℂ) * y))‖ ≤
      r ^ ((m + 1) * (2 * n')) / (((m + 1) * (2 * n')).factorial : ℝ) *
        (1 / (1 - (n' : ℝ) * r / (((m + 1) * (2 * n') : ℕ) + 1)) ^ ((m + 1) * (2 * n') + m + 1)) := by
  set M0 := (m + 1) * (2 * n') with hM0
  set N := M0 + m with hN
  set z : ℝ := (n' : ℝ) * r / ((M0 : ℕ) + 1) with hzdef
  have hr0 : 0 ≤ r := (norm_nonneg y).trans hy
  have hz0 : 0 ≤ z := by positivity
  have hcard : (m + 1) * (nodes n').card - 1 = N := by
    rw [card_nodes, hN, hM0, Nat.mul_succ]; omega
  set c : ℕ → ℂ := fun L => ((tau m (nodes n') h L / (L.factorial : ℚ) : ℚ) : ℂ) * y ^ L with hc
  have hS := R_hasSum m n' h y
  rw [← hasSum_nat_add_iff' (N - h)] at hS
  have hzero : ∑ i ∈ Finset.range (N - h), c i = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    rw [Finset.mem_range] at hL
    rw [hc]
    beta_reduce
    rw [tau_eq_zero (h := h) (l := L) (nodes_nonempty n') (by rw [hcard]; omega)]
    simp
  rw [hzero, sub_zero] at hS
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) N
    (r := z) (by rw [Real.norm_eq_abs, abs_of_nonneg hz0]; exact hz)).mul_left
      (r ^ M0 / (M0.factorial : ℝ))
  refine hS.norm_le_of_bounded hg fun k => ?_
  rw [norm_mul, norm_pow, Complex.norm_ratCast]
  have hl : (m + 1) * (nodes n').card - 1 ≤ k + (N - h) + h := by rw [hcard]; omega
  have htau := tau_bound (m := m) (nodes_nonempty n') (n' : ℚ)
    (fun k hk => abs_le_of_mem_nodes hk) hl
  rw [hcard, show k + (N - h) + h - N = k by omega, show k + (N - h) + h = k + N by omega] at htau
  have htauR : |(tau m (nodes n') h (k + (N - h)) : ℝ)| ≤ ((k + N).choose N : ℝ) * (n' : ℝ) ^ k := by
    exact_mod_cast htau
  rw [Rat.cast_div, Rat.cast_natCast, abs_div, Nat.abs_cast]
  have hpow : ‖y‖ ^ (k + (N - h)) ≤ r ^ (k + (N - h)) := pow_le_pow_left₀ (norm_nonneg _) hy _
  have hfac := pow_div_factorial_le hr0 M0 (k + (N - h) - M0)
  rw [show M0 + (k + (N - h) - M0) = k + (N - h) by omega] at hfac
  have hq1 : r / ((M0 : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hr
  have hq2 : (r / ((M0 : ℝ) + 1)) ^ (k + (N - h) - M0) ≤ (r / ((M0 : ℝ) + 1)) ^ k :=
    pow_le_pow_of_le_one (by positivity) hq1 (by omega)
  have hzk : z ^ k = (n' : ℝ) ^ k * (r / ((M0 : ℝ) + 1)) ^ k := by
    rw [hzdef, ← mul_pow, mul_div_assoc]
  calc |(tau m (nodes n') h (k + (N - h)) : ℝ)| / ((k + (N - h)).factorial : ℝ) *
        ‖y‖ ^ (k + (N - h))
      ≤ ((k + N).choose N : ℝ) * (n' : ℝ) ^ k * (r ^ (k + (N - h)) /
          ((k + (N - h)).factorial : ℝ)) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        apply mul_le_mul htauR _ (by positivity) (by positivity)
        exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ ((k + N).choose N : ℝ) * (n' : ℝ) ^ k * (r ^ M0 / (M0.factorial : ℝ) *
          (r / ((M0 : ℝ) + 1)) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hfac.trans (mul_le_mul_of_nonneg_left hq2 (by positivity))
    _ = r ^ M0 / (M0.factorial : ℝ) * (((k + N).choose N : ℕ) * z ^ k) := by
        rw [hzk]; ring

end PiMahler

end PartAnalytic

section PartCore

/-!
# The Diophantine core

Combining non-vanishing, integrality and the analytic bound into an explicit lower
bound for `|π - p/q|`.
-/

namespace PiMahler

open Complex

variable (m n' : ℕ)

/-- Gaussian integers inside `ℂ`. -/
def IsGI (w : ℂ) : Prop := ∃ a b : ℤ, w = a + b * I

lemma IsGI.add {w v : ℂ} (hw : IsGI w) (hv : IsGI v) : IsGI (w + v) := by
  obtain ⟨a, b, rfl⟩ := hw; obtain ⟨c, d, rfl⟩ := hv
  exact ⟨a + c, b + d, by push_cast; ring⟩

lemma IsGI.mul {w v : ℂ} (hw : IsGI w) (hv : IsGI v) : IsGI (w * v) := by
  obtain ⟨a, b, rfl⟩ := hw; obtain ⟨c, d, rfl⟩ := hv
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  push_cast
  linear_combination (b * d : ℂ) * I_sq

lemma IsGI.intCast (a : ℤ) : IsGI (a : ℂ) := ⟨a, 0, by simp⟩

lemma IsGI.natCast (a : ℕ) : IsGI (a : ℂ) := ⟨a, 0, by simp⟩

lemma IsGI.I : IsGI Complex.I := ⟨0, 1, by simp⟩

lemma IsGI.pow {w : ℂ} (hw : IsGI w) : ∀ k : ℕ, IsGI (w ^ k)
  | 0 => ⟨1, 0, by simp⟩
  | k + 1 => by rw [pow_succ]; exact (hw.pow k).mul hw

lemma IsGI.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsGI (f i)) :
    IsGI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma IsGI.one_le_norm {w : ℂ} (hw : IsGI w) (h0 : w ≠ 0) : 1 ≤ ‖w‖ := by
  obtain ⟨a, b, rfl⟩ := hw
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc; push_neg at hc; apply h0; rw [hc.1, hc.2]; simp
  have hsq : (1 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    rcases hab with ha | hb
    · have : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ a ^ 2 := by nlinarith [sq_nonneg a, Int.one_le_abs ha, sq_abs a]
        exact_mod_cast this
      nlinarith [sq_nonneg (b : ℝ)]
    · have : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ b ^ 2 := by nlinarith [sq_nonneg b, Int.one_le_abs hb, sq_abs b]
        exact_mod_cast this
      nlinarith [sq_nonneg (a : ℝ)]
  have hn : ‖((a : ℂ) + (b : ℂ) * Complex.I)‖ = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp; ring
  rw [hn]
  exact Real.one_le_sqrt.2 hsq

/-- The coefficients `A_s = ∑_i a h (i-n') s · I^i`. -/
noncomputable def Acoef (h s : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (2 * n' + 1), (aa m n' h (nodeEmb n' i) s : ℂ) * Complex.I ^ i

/-- The auxiliary polynomial `S_h(Y) = ∑_s A_s Y^s`. -/
noncomputable def Sfun (h : ℕ) (Y : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (m + 1), Acoef m n' h s * Y ^ s

/-- The auxiliary function `R_h(y)`. -/
noncomputable def Rfun (h : ℕ) (y : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (2 * n' + 1), ∑ s ∈ Finset.range (m + 1),
    (aa m n' h (nodeEmb n' i) s : ℂ) * (y ^ s * Complex.exp (((nodeEmb n' i : ℤ) : ℂ) * y))

lemma Rfun_eq_Sfun (h : ℕ) :
    Rfun m n' h ((Real.pi / 2 : ℝ) * I) =
      Complex.exp (-((n' : ℂ) * ((Real.pi / 2 : ℝ) * I))) * Sfun m n' h ((Real.pi / 2 : ℝ) * I) := by
  set Y : ℂ := (Real.pi / 2 : ℝ) * I with hY
  have hexp : ∀ i : ℕ, Complex.exp (((nodeEmb n' i : ℤ) : ℂ) * Y) =
      Complex.exp (-((n' : ℂ) * Y)) * Complex.I ^ i := by
    intro i
    have : Complex.I ^ i = Complex.exp ((i : ℂ) * Y) := by
      rw [show (i : ℂ) * Y = (i : ℕ) * (Real.pi / 2 * I) by rw [hY]; push_cast; ring,
        Complex.exp_nat_mul]
      congr 1
      rw [show (Real.pi / 2 * I : ℂ) = (Real.pi / 2 : ℂ) * I by ring, Complex.exp_mul_I]
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    rw [this, ← Complex.exp_add, nodeEmb_apply]
    congr 1; push_cast; ring
  unfold Rfun Sfun Acoef
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hexp]; ring

lemma norm_Sfun_eq_Rfun (h : ℕ) :
    ‖Sfun m n' h ((Real.pi / 2 : ℝ) * I)‖ = ‖Rfun m n' h ((Real.pi / 2 : ℝ) * I)‖ := by
  rw [Rfun_eq_Sfun, norm_mul, Complex.norm_exp]
  simp

lemma Acoef_GI (h s : ℕ) (hs : s ≤ m) : IsGI ((Knorm m n' : ℂ) * Acoef m n' h s) := by
  unfold Acoef
  rw [Finset.mul_sum]
  apply IsGI.sum
  intro i hi
  obtain ⟨z, hz⟩ := aa_int m n' h s hs i (by have := Finset.mem_range.1 hi; omega)
  rw [← mul_assoc]
  have : (Knorm m n' : ℂ) * (aa m n' h (nodeEmb n' i) s : ℂ) = (z : ℂ) := by
    have := congrArg (fun x : ℚ => (x : ℂ)) hz
    push_cast at this; exact this
  rw [this]
  exact (IsGI.intCast z).mul (IsGI.I.pow i)

lemma Sfun_GI (h : ℕ) (p q : ℕ) (hq : 0 < q) :
    IsGI (((2 * q : ℕ) : ℂ) ^ m * (Knorm m n' : ℂ) *
      Sfun m n' h (((p : ℝ) / (2 * q) : ℝ) * I)) := by
  unfold Sfun
  rw [Finset.mul_sum]
  apply IsGI.sum
  intro s hs
  have hs' : s ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  have hq2 : ((2 * q : ℕ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * q := by positivity
    exact_mod_cast this.ne'
  have : ((2 * q : ℕ) : ℂ) ^ m * (Knorm m n' : ℂ) *
      (Acoef m n' h s * ((((p : ℝ) / (2 * q) : ℝ) : ℂ) * I) ^ s) =
      ((Knorm m n' : ℂ) * Acoef m n' h s) * (((p : ℂ) * I) ^ s * ((2 * q : ℕ) : ℂ) ^ (m - s)) := by
    have e : ((2 * q : ℕ) : ℂ) ^ m = ((2 * q : ℕ) : ℂ) ^ (m - s) * ((2 * q : ℕ) : ℂ) ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hs']
    have hy : ((((p : ℝ) / (2 * q) : ℝ)) : ℂ) = (p : ℂ) / ((2 * q : ℕ) : ℂ) := by push_cast; ring
    rw [hy, e, mul_pow, mul_pow, div_pow]
    have : ((2 * q : ℕ) : ℂ) ^ s * ((p : ℂ) ^ s / ((2 * q : ℕ) : ℂ) ^ s) = (p : ℂ) ^ s :=
      mul_div_cancel₀ _ (pow_ne_zero _ hq2)
    linear_combination (↑(Knorm m n') * Acoef m n' h s * I ^ s * ((2 * q : ℕ) : ℂ) ^ (m - s)) * this
  rw [this]
  exact (Acoef_GI m n' h s hs').mul
    (((IsGI.natCast p).mul IsGI.I).pow s |>.mul ((IsGI.natCast _).pow _))

lemma norm_pow_sub_pow_le (a b : ℂ) (ρ : ℝ) (ha : ‖a‖ ≤ ρ) (hb : ‖b‖ ≤ ρ) (s : ℕ) :
    ‖a ^ s - b ^ s‖ ≤ s * ρ ^ (s - 1) * ‖a - b‖ := by
  have hρ : 0 ≤ ρ := (norm_nonneg a).trans ha
  rw [← geom_sum₂_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range s, ‖a ^ i * b ^ (s - 1 - i)‖ ≤ ∑ _i ∈ Finset.range s, ρ ^ (s - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.1 hi
        rw [norm_mul, norm_pow, norm_pow, show s - 1 = i + (s - 1 - i) by omega, pow_add]
        rw [show i + (s - 1 - i) - i = s - 1 - i by omega]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
          (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (by positivity)
    _ = s * ρ ^ (s - 1) := by simp

lemma norm_Sfun_sub_le (h : ℕ) (a b : ℂ) (ha : ‖a‖ ≤ 2) (hb : ‖b‖ ≤ 2) :
    ‖Sfun m n' h a - Sfun m n' h b‖ ≤
      (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1))) * ‖a - b‖ := by
  unfold Sfun
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le a b 2 ha hb s) (norm_nonneg _)

/-- Bound for the scaled coefficients `K · A_s`. -/
noncomputable def Wb : ℝ :=
  (2 : ℝ) ^ (2 * n' * (m + 1)) * (lcmUpTo (2 * n') : ℝ) ^ m * (m.factorial : ℝ) *
    ((n' : ℝ) + 1) ^ m * (((m + 1) * (2 * n') + m).choose ((m + 1) * (2 * n')) : ℝ)

lemma choose_pow_le (i : ℕ) :
    ((2 * n').choose i : ℝ) ^ (m + 1) ≤ ((2 * n').choose i : ℝ) * ((2 : ℝ) ^ (2 * n')) ^ m := by
  rw [pow_succ']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast Nat.choose_le_two_pow _ _

lemma norm_K_Acoef_le (h s : ℕ) (hs : s ≤ m) (hh : h ≤ m) :
    (Knorm m n' : ℝ) * ‖Acoef m n' h s‖ ≤ Wb m n' := by
  unfold Acoef Wb
  rw [show (Knorm m n' : ℝ) = ‖(Knorm m n' : ℂ)‖ by simp, ← norm_mul, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  set W : ℝ := (lcmUpTo (2 * n') : ℝ) ^ m * (m.factorial : ℝ) *
    ((n' : ℝ) + 1) ^ m * (((m + 1) * (2 * n') + m).choose ((m + 1) * (2 * n')) : ℝ) with hW
  calc ∑ i ∈ Finset.range (2 * n' + 1),
        ‖(Knorm m n' : ℂ) * ((aa m n' h (nodeEmb n' i) s : ℂ) * Complex.I ^ i)‖
      ≤ ∑ i ∈ Finset.range (2 * n' + 1), ((2 * n').choose i : ℝ) ^ (m + 1) * W := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := aa_bound m n' h s hs hh i (by have := Finset.mem_range.1 hi; omega)
        rw [← mul_assoc, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
        have : ‖(Knorm m n' : ℂ) * (aa m n' h (nodeEmb n' i) s : ℂ)‖ =
            |(((Knorm m n' : ℚ) * aa m n' h (nodeEmb n' i) s : ℚ) : ℝ)| := by
          have e : (Knorm m n' : ℂ) * (aa m n' h (nodeEmb n' i) s : ℂ) =
              ((((Knorm m n' : ℚ) * aa m n' h (nodeEmb n' i) s : ℚ) : ℝ) : ℂ) := by
            push_cast; ring
          rw [e, Complex.norm_real, Real.norm_eq_abs]
        rw [this, hW]
        have hb' := (Rat.cast_le (K := ℝ)).2 hb
        rw [Rat.cast_abs] at hb'
        refine hb'.trans (le_of_eq ?_)
        push_cast; ring
    _ ≤ ∑ i ∈ Finset.range (2 * n' + 1), ((2 * n').choose i : ℝ) * ((2 : ℝ) ^ (2 * n')) ^ m * W := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (choose_pow_le m n' i) (by positivity)
    _ = (2 : ℝ) ^ (2 * n') * ((2 : ℝ) ^ (2 * n')) ^ m * W := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        have := Nat.sum_range_choose (2 * n')
        exact_mod_cast this
    _ = _ := by rw [hW, ← pow_mul, ← pow_add]; ring_nf

/-- `T = (∑_s s 2^(s-1)) · Wb`. -/
noncomputable def Tb : ℝ :=
  (∑ s ∈ Finset.range (m + 1), (s : ℝ) * 2 ^ (s - 1)) * Wb m n'

/-- `Eb = r^M₀ / M₀! · (1 - z)^{-(N+1)}` with `r = π/2`. -/
noncomputable def Eb : ℝ :=
  (Real.pi / 2) ^ ((m + 1) * (2 * n')) / (((m + 1) * (2 * n')).factorial : ℝ) *
    (1 / (1 - (n' : ℝ) * (Real.pi / 2) / (((m + 1) * (2 * n') : ℕ) + 1)) ^
      ((m + 1) * (2 * n') + m + 1))

/-- **Core inequality.** -/
theorem core (p q : ℕ) (hq : 0 < q) (hpq : p < 4 * q)
    (hr : Real.pi / 2 ≤ ((m + 1) * (2 * n') : ℕ) + 1)
    (hz : (n' : ℝ) * (Real.pi / 2) / (((m + 1) * (2 * n') : ℕ) + 1) < 1)
    (hE : 2 * (Knorm m n' : ℝ) * ((2 * q : ℕ) : ℝ) ^ m * Eb m n' ≤ 1) :
    1 / (((2 * q : ℕ) : ℝ) ^ m * Tb m n') ≤ |Real.pi - (p : ℝ) / q| := by
  set Y : ℂ := (Real.pi / 2 : ℝ) * I with hY
  set y0 : ℂ := (((p : ℝ) / (2 * q) : ℝ) : ℂ) * I with hy0
  obtain ⟨h, hS⟩ := exists_S_ne_zero m n' y0
  have hSy0 : Sfun m n' h y0 ≠ 0 := by
    unfold Sfun Acoef
    rw [← Fin.sum_univ_eq_sum_range (fun s => (∑ i ∈ Finset.range (2 * n' + 1),
      (aa m n' h (nodeEmb n' i) s : ℂ) * Complex.I ^ i) * y0 ^ s)]
    exact hS
  have hh : (h : ℕ) ≤ m := Nat.lt_succ_iff.1 h.2
  set K : ℝ := (Knorm m n' : ℝ) with hK
  have hK0 : 0 < K := by
    rw [hK]; unfold Knorm
    have := lcmUpTo_pos (2 * n')
    positivity
  have hKn : Knorm m n' ≠ 0 := by
    have := hK0; rw [hK] at this; exact_mod_cast this.ne'
  set Q : ℝ := ((2 * q : ℕ) : ℝ) ^ m with hQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  -- lower bound from integrality
  have hlow : 1 ≤ Q * K * ‖Sfun m n' h y0‖ := by
    have hGI := Sfun_GI m n' h p q hq
    have := hGI.one_le_norm (by
      apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by
        have : (0 : ℝ) < 2 * q := by positivity
        exact_mod_cast this.ne')) (Nat.cast_ne_zero.2 hKn)) hSy0)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast] at this
    exact this
  -- analytic upper bound at `Y`
  have hY1 : ‖Sfun m n' h Y‖ ≤ Eb m n' := by
    rw [hY, norm_Sfun_eq_Rfun]
    unfold Rfun Eb
    apply R_bound m n' h hh _ _ _ hr hz
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  -- difference
  have hpi4 := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have hy0n : ‖y0‖ ≤ 2 := by
    rw [hy0, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : (p : ℝ) < 4 * q := by exact_mod_cast hpq
    linarith
  have hYn : ‖Y‖ ≤ 2 := by
    rw [hY, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hdiff := norm_Sfun_sub_le m n' h y0 Y hy0n hYn
  have hyY : ‖y0 - Y‖ = |Real.pi - (p : ℝ) / q| / 2 := by
    rw [hy0, hY, ← sub_mul, ← Complex.ofReal_sub, Complex.norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, show (p : ℝ) / (2 * q) - Real.pi / 2 =
        -((Real.pi - (p : ℝ) / q) / 2) by field_simp; ring, abs_neg, abs_div,
      abs_two]
  have hT : K * (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1))) ≤
      Tb m n' := by
    unfold Tb
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    have hs' : s ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have := norm_K_Acoef_le m n' h s hs' hh
    rw [← hK] at this
    calc K * (‖Acoef m n' h s‖ * (s * 2 ^ (s - 1))) =
        (K * ‖Acoef m n' h s‖) * (s * 2 ^ (s - 1)) := by ring
      _ ≤ Wb m n' * (s * 2 ^ (s - 1)) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  -- combine
  set δ := |Real.pi - (p : ℝ) / q| with hδ
  have htri : ‖Sfun m n' h y0‖ ≤ ‖Sfun m n' h Y‖ +
      ‖Sfun m n' h y0 - Sfun m n' h Y‖ := by
    have := norm_add_le (Sfun m n' h Y) (Sfun m n' h y0 - Sfun m n' h Y)
    simpa using this
  have hE' : Q * K * Eb m n' ≤ 1 / 2 := by
    have : 2 * K * Q * Eb m n' ≤ 1 := hE
    linarith
  have hEb0 : 0 ≤ Eb m n' := (norm_nonneg _).trans hY1
  have key : 1 ≤ 1 / 2 + Q * (Tb m n' * (δ / 2)) := by
    have h1 : Q * K * ‖Sfun m n' h y0‖ ≤ Q * K * Eb m n' +
        Q * (K * (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1)))) *
          (δ / 2) := by
      rw [← hyY]
      have := mul_le_mul_of_nonneg_left (htri.trans (add_le_add hY1 hdiff))
        (le_of_lt (mul_pos hQ0 hK0))
      linarith
    have h2 : Q * (K * (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1)))) *
        (δ / 2) ≤ Q * (Tb m n' * (δ / 2)) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hQ0.le
      exact mul_le_mul_of_nonneg_right hT (by positivity)
    linarith
  have hTpos : 0 < Q * Tb m n' := by
    by_contra hneg
    push_neg at hneg
    nlinarith [abs_nonneg (Real.pi - (p : ℝ) / q)]
  rw [div_le_iff₀ hTpos]
  nlinarith

end PiMahler

end PartCore

section PartNumerics

/-!
# Numerical inequalities

Explicit inequalities for all `n' ≥ n₀`, proved by checking a base case and showing that
the sequence decreases.
-/

namespace PiMahler

lemma le_one_of_step (a : ℕ → ℝ) (n0 : ℕ) (h0 : a n0 ≤ 1)
    (hs : ∀ n ≥ n0, a (n + 1) ≤ a n) : ∀ n ≥ n0, a n ≤ 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h0
  | succ k hk ih => exact (hs k hk).trans ih

/-- `C₀ · ((2n)!)^11 / (22n)! · B^n`. -/
noncomputable def fseq (C0 B : ℝ) (n : ℕ) : ℝ :=
  C0 * ((2 * n).factorial : ℝ) ^ 11 / ((22 * n).factorial : ℝ) * B ^ n

lemma factorial_add_ge (a k : ℕ) :
    ((a.factorial : ℝ)) * ((a : ℝ) + 1) ^ k ≤ ((a + k).factorial : ℝ) := by
  rw [← Nat.factorial_mul_ascFactorial]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := Nat.pow_succ_le_ascFactorial (a + 1) k
  exact_mod_cast this

lemma fseq_key (B b x : ℝ) (hb : 0 ≤ b) (hx : 0 ≤ x) (hBb : B ≤ b ^ 22)
    (hn : b * (2 * x + 2) ≤ 22 * x + 1) :
    B * ((2 * x + 1) * (2 * x + 2)) ^ 11 ≤ (22 * x + 1) ^ 22 := by
  have hx2 : (2 * x + 1) * (2 * x + 2) ≤ (2 * x + 2) ^ 2 := by nlinarith
  have e1 : ((2 * x + 1) * (2 * x + 2)) ^ 11 ≤ ((2 * x + 2) ^ 2) ^ 11 :=
    pow_le_pow_left₀ (by positivity) hx2 _
  calc B * ((2 * x + 1) * (2 * x + 2)) ^ 11 ≤ b ^ 22 * ((2 * x + 2) ^ 2) ^ 11 :=
        mul_le_mul hBb e1 (by positivity) (by positivity)
    _ = (b * (2 * x + 2)) ^ 22 := by ring
    _ ≤ (22 * x + 1) ^ 22 := pow_le_pow_left₀ (by positivity) hn _

lemma fseq_alg (C0 B F2 F22 G22 x : ℝ) (hC : 0 ≤ C0) (hB : 0 ≤ B) (hF2 : 0 ≤ F2)
    (hF22 : 0 < F22) (hG22 : 0 < G22)
    (hkey : B * ((2 * x + 1) * (2 * x + 2)) ^ 11 ≤ (22 * x + 1) ^ 22)
    (h22 : F22 * (22 * x + 1) ^ 22 ≤ G22) (n : ℕ) :
    C0 * (F2 * ((2 * x + 1) * (2 * x + 2))) ^ 11 / G22 * B ^ (n + 1) ≤
      C0 * F2 ^ 11 / F22 * B ^ n := by
  have hG : F22 * (B * ((2 * x + 1) * (2 * x + 2)) ^ 11) ≤ G22 :=
    (mul_le_mul_of_nonneg_left hkey hF22.le).trans h22
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hG22 hF22]
  calc C0 * (F2 * ((2 * x + 1) * (2 * x + 2))) ^ 11 * B ^ (n + 1) * F22
      = (C0 * F2 ^ 11 * B ^ n) * (F22 * (B * ((2 * x + 1) * (2 * x + 2)) ^ 11)) := by ring
    _ ≤ (C0 * F2 ^ 11 * B ^ n) * G22 :=
        mul_le_mul_of_nonneg_left hG (by positivity)

lemma fseq_step (C0 B b : ℝ) (hC : 0 ≤ C0) (hB : 0 ≤ B) (hb : 0 ≤ b) (hBb : B ≤ b ^ 22)
    (n : ℕ) (hn : b * (2 * n + 2) ≤ 22 * n + 1) : fseq C0 B (n + 1) ≤ fseq C0 B n := by
  unfold fseq
  have h2 : ((2 * (n + 1)).factorial : ℝ) = ((2 * n).factorial : ℝ) * ((2 * n + 1) * (2 * n + 2)) := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have h22 := factorial_add_ge (22 * n) 22
  rw [show 22 * n + 22 = 22 * (n + 1) by ring] at h22
  push_cast at h22
  rw [h2]
  have key := fseq_key B b n hb (Nat.cast_nonneg n) hBb hn
  exact fseq_alg C0 B ((2 * n).factorial : ℝ) ((22 * n).factorial : ℝ)
    ((22 * (n + 1)).factorial : ℝ) (n : ℝ) hC hB (Nat.cast_nonneg _)
    (Nat.cast_pos.2 (Nat.factorial_pos _)) (Nat.cast_pos.2 (Nat.factorial_pos _)) key h22 n

/-- `C₁ · ((n+1)(22n+10))^10 · G^n`. -/
noncomputable def gseq (C1 G : ℝ) (n : ℕ) : ℝ :=
  C1 * (((n : ℝ) + 1) * (22 * n + 10)) ^ 10 * G ^ n

lemma gseq_step (C1 G γ : ℝ) (hC : 0 ≤ C1) (hG : 0 ≤ G) (hγ : 0 ≤ γ) (hGγ : G ≤ γ ^ 10)
    (n : ℕ) (hn : γ * ((n + 2) * (22 * n + 32)) ≤ (n + 1) * (22 * n + 10)) :
    gseq C1 G (n + 1) ≤ gseq C1 G n := by
  unfold gseq
  push_cast
  have hkey : (((n : ℝ) + 1 + 1) * (22 * (n + 1) + 10)) ^ 10 * G ≤
      (((n : ℝ) + 1) * (22 * n + 10)) ^ 10 := by
    calc (((n : ℝ) + 1 + 1) * (22 * (n + 1) + 10)) ^ 10 * G
        ≤ (((n : ℝ) + 1 + 1) * (22 * (n + 1) + 10)) ^ 10 * γ ^ 10 :=
          mul_le_mul_of_nonneg_left hGγ (by positivity)
      _ = (γ * ((n + 2) * (22 * n + 32))) ^ 10 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hn _
  calc C1 * (((n : ℝ) + 1 + 1) * (22 * (n + 1) + 10)) ^ 10 * G ^ (n + 1)
      = C1 * G ^ n * ((((n : ℝ) + 1 + 1) * (22 * (n + 1) + 10)) ^ 10 * G) := by ring
    _ ≤ C1 * G ^ n * (((n : ℝ) + 1) * (22 * n + 10)) ^ 10 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-! ### Concrete constants -/

/-- `ρ = 1.5708 ≥ π/2`. -/
noncomputable def rhoC : ℝ := 3927 / 2500
/-- `c = 1/(1 - ρ/22)`. -/
noncomputable def cC : ℝ := 55000 / 51073
/-- `v ≥ 10^(2.9245·20/9)`. -/
noncomputable def vC : ℝ := 3162300
/-- `u ≤ 10^(8.9101·20/9)`. -/
noncomputable def uC : ℝ := 63 * 10 ^ 18

noncomputable def C0f : ℝ := 2 ^ 11 * 3628800 * cC ^ 11 * vC
noncomputable def Bf (β : ℝ) : ℝ := β ^ 20 * rhoC ^ 22 * cC ^ 22 * vC

theorem fseq3_le_one : ∀ n ≥ 22, fseq C0f (Bf 3) n ≤ 1 := by
  apply le_one_of_step _ 22
  · unfold fseq C0f Bf cC vC rhoC
    norm_num [Nat.factorial]
  · intro n hn
    apply fseq_step C0f (Bf 3) (91 / 10) (by unfold C0f cC vC; positivity)
      (by unfold Bf cC vC rhoC; positivity) (by norm_num)
      (by unfold Bf cC vC rhoC; norm_num)
    have : (22 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

theorem fseq349_le_one : ∀ n ≥ 100, fseq C0f (Bf 3.49) n ≤ 1 := by
  apply le_one_of_step _ 100
  · unfold fseq C0f Bf cC vC rhoC
    norm_num [Nat.factorial]
  · intro n hn
    apply fseq_step C0f (Bf 3.49) (105 / 10) (by unfold C0f cC vC; positivity)
      (by unfold Bf cC vC rhoC; positivity) (by norm_num)
      (by unfold Bf cC vC rhoC; norm_num)
    have : (100 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

noncomputable def C1g : ℝ := 2 ^ 11 * 9217
noncomputable def Gg : ℝ := 2 ^ 22 * (3.49 : ℝ) ^ 20 / uC

theorem gseq_le_one : ∀ n ≥ 22, gseq C1g Gg n ≤ 1 := by
  apply le_one_of_step _ 22
  · unfold gseq C1g Gg uC
    norm_num
  · intro n hn
    apply gseq_step C1g Gg (59 / 100) (by unfold C1g; positivity)
      (by unfold Gg uC; positivity) (by norm_num) (by unfold Gg uC; norm_num)
    have : (22 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-! ### Powers of ten -/

lemma ten_rpow_le_v : (10 : ℝ) ^ ((2.9245 : ℝ) * 20 / 9) ≤ vC := by
  have h1 : (10 : ℝ) ^ ((2.9245 : ℝ) * 20 / 9) ≤ (10 : ℝ) ^ ((6 : ℝ) + 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  refine h1.trans ?_
  rw [Real.rpow_add (by norm_num)]
  have h2 : (10 : ℝ) ^ ((1 : ℝ) / 2) ≤ 31623 / 10000 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  unfold vC
  have : (10 : ℝ) ^ ((6 : ℕ) : ℝ) = 10 ^ 6 := Real.rpow_natCast _ _
  rw [show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, this]
  nlinarith

lemma u_le_ten_rpow : uC ≤ (10 : ℝ) ^ ((8.9101 : ℝ) * 20 / 9) := by
  have h1 : (10 : ℝ) ^ ((19 : ℝ) + 4 / 5) ≤ (10 : ℝ) ^ ((8.9101 : ℝ) * 20 / 9) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  refine le_trans ?_ h1
  rw [Real.rpow_add (by norm_num)]
  have h2 : (63 / 10 : ℝ) ≤ (10 : ℝ) ^ ((4 : ℝ) / 5) := by
    have hp : 0 ≤ (10 : ℝ) ^ ((4 : ℝ) / 5) := by positivity
    have h5 : ((10 : ℝ) ^ ((4 : ℝ) / 5)) ^ (5 : ℕ) = 10 ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra hc
    push_neg at hc
    have : ((10 : ℝ) ^ ((4 : ℝ) / 5)) ^ (5 : ℕ) < (63 / 10 : ℝ) ^ (5 : ℕ) :=
      pow_lt_pow_left₀ hc hp (by norm_num)
    rw [h5] at this
    norm_num at this
  unfold uC
  have : (10 : ℝ) ^ ((19 : ℕ) : ℝ) = 10 ^ 19 := Real.rpow_natCast _ _
  rw [show ((19 : ℝ)) = ((19 : ℕ) : ℝ) by norm_num, this]
  nlinarith

end PiMahler

end PartNumerics

section PartFinal

/-!
# Mahler's bound (1953, eq. 13)
-/

namespace PiMahler

lemma pi_div_two_le_rho : Real.pi / 2 ≤ rhoC := by
  have := Real.pi_lt_d4
  unfold rhoC; linarith

lemma Knorm_le (n' : ℕ) (β : ℝ) (hβ : (lcmUpTo (2 * n') : ℝ) ≤ β ^ (2 * n')) :
    (Knorm 10 n' : ℝ) ≤ ((2 * n').factorial : ℝ) ^ 11 * (β ^ 20) ^ n' * 3628800 := by
  unfold Knorm
  push_cast
  have h10 : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
  rw [h10]
  have hD : (lcmUpTo (2 * n') : ℝ) ^ 10 ≤ (β ^ 20) ^ n' := by
    calc (lcmUpTo (2 * n') : ℝ) ^ 10 ≤ (β ^ (2 * n')) ^ 10 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hβ _
      _ = (β ^ 20) ^ n' := by rw [← pow_mul, ← pow_mul]; ring_nf
  gcongr

lemma Eb_le (n' : ℕ) :
    Eb 10 n' ≤ rhoC ^ (22 * n') / ((22 * n').factorial : ℝ) * cC ^ (22 * n' + 11) := by
  unfold Eb
  have hrho := pi_div_two_le_rho
  have hpi := Real.pi_pos
  rw [show (10 + 1) * (2 * n') = 22 * n' by ring, show 22 * n' + 10 + 1 = 22 * n' + 11 by ring]
  have hz : (n' : ℝ) * (Real.pi / 2) / (((22 * n' : ℕ) : ℝ) + 1) ≤ rhoC / 22 := by
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have : (n' : ℝ) * (Real.pi / 2) ≤ n' * rhoC :=
      mul_le_mul_of_nonneg_left hrho (Nat.cast_nonneg _)
    have : 0 ≤ rhoC := by unfold rhoC; norm_num
    nlinarith
  have h1 : 1 / cC ≤ 1 - (n' : ℝ) * (Real.pi / 2) / (((22 * n' : ℕ) : ℝ) + 1) := by
    have : 1 / cC = 1 - rhoC / 22 := by unfold cC rhoC; norm_num
    rw [this]; linarith
  have hc0 : 0 < 1 / cC := by unfold cC; norm_num
  have h2 : 1 / (1 - (n' : ℝ) * (Real.pi / 2) / (((22 * n' : ℕ) : ℝ) + 1)) ^ (22 * n' + 11) ≤
      cC ^ (22 * n' + 11) := by
    rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le hc0 h1) _)]
    calc (1 : ℝ) = cC ^ (22 * n' + 11) * (1 / cC) ^ (22 * n' + 11) := by
          rw [← mul_pow, mul_one_div_cancel (by unfold cC; norm_num), one_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le h1 _) (by unfold cC; positivity)
  have h3 : (Real.pi / 2) ^ (22 * n') ≤ rhoC ^ (22 * n') :=
    pow_le_pow_left₀ (by positivity) hrho _
  have hpos : 0 < 1 - (n' : ℝ) * (Real.pi / 2) / (((22 * n' : ℕ) : ℝ) + 1) := lt_of_lt_of_le hc0 h1
  have hr0 : 0 ≤ rhoC := by unfold rhoC; norm_num
  exact mul_le_mul (div_le_div_of_nonneg_right h3 (by positivity)) h2 (by positivity)
    (by positivity)

lemma two_pow_mul_Tb_le (n' : ℕ) :
    2 ^ 10 * Tb 10 n' ≤ gseq C1g Gg n' * uC ^ n' / 2 := by
  unfold Tb Wb gseq C1g Gg
  have hs : (∑ s ∈ Finset.range (10 + 1), (s : ℝ) * 2 ^ (s - 1)) = 9217 := by
    norm_num [Finset.sum_range_succ]
  rw [hs]
  have hD : (lcmUpTo (2 * n') : ℝ) ^ 10 ≤ ((3.49 : ℝ) ^ 20) ^ n' := by
    calc (lcmUpTo (2 * n') : ℝ) ^ 10 ≤ ((3.49 : ℝ) ^ (2 * n')) ^ 10 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (lcmUpTo_le_real _) _
      _ = ((3.49 : ℝ) ^ 20) ^ n' := by rw [← pow_mul, ← pow_mul]; ring_nf
  have hC : ((((10 + 1) * (2 * n') + 10).choose ((10 + 1) * (2 * n')) : ℕ) : ℝ) ≤
      ((22 * n' : ℝ) + 10) ^ 10 / 3628800 := by
    rw [Nat.choose_symm_add]
    have := Nat.choose_le_pow_div (α := ℝ) 10 ((10 + 1) * (2 * n') + 10)
    have h10 : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
    rw [h10] at this
    refine this.trans (le_of_eq ?_)
    push_cast; ring_nf
  have h10 : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
  rw [h10]
  have hu : (0 : ℝ) < uC := by unfold uC; norm_num
  calc (2 : ℝ) ^ 10 * (9217 * ((2 : ℝ) ^ (2 * n' * (10 + 1)) * (lcmUpTo (2 * n') : ℝ) ^ 10 *
        3628800 * ((n' : ℝ) + 1) ^ 10 *
        ((((10 + 1) * (2 * n') + 10).choose ((10 + 1) * (2 * n')) : ℕ) : ℝ)))
      ≤ (2 : ℝ) ^ 10 * (9217 * ((2 : ℝ) ^ (2 * n' * (10 + 1)) * ((3.49 : ℝ) ^ 20) ^ n' *
        3628800 * ((n' : ℝ) + 1) ^ 10 * (((22 * n' : ℝ) + 10) ^ 10 / 3628800))) := by
        gcongr
    _ = _ := by
        rw [div_pow, show 2 * n' * (10 + 1) = 22 * n' by ring, pow_mul,
          mul_pow ((2 : ℝ) ^ 22) ((3.49 : ℝ) ^ 20) n']
        generalize ((2 : ℝ) ^ 22) ^ n' = T
        generalize ((3.49 : ℝ) ^ 20) ^ n' = A
        have hu' : uC ^ n' ≠ 0 := pow_ne_zero _ hu.ne'
        field_simp

end PiMahler

open PiMahler in
theorem mahler_reference_solution (p q n : ℕ) (_hp : 0 < p) (hq : 0 < q)
    (hpq : p < 4 * q) (hn : 50 ≤ n)
    (hnq : (q : ℝ) ^ 10 < (10 : ℝ) ^ ((2.9245 : ℝ) * n)) :
    (10 : ℝ) ^ (-((8.9101 : ℝ) * n)) / (q : ℝ) ^ 10 < |Real.pi - (p : ℝ) / (q : ℝ)| := by
  set n' := 9 * n / 20 with hn'def
  have hn' : 22 ≤ n' := by omega
  have h9 : 9 * n < 20 * (n' + 1) := by omega
  have h20 : 20 * n' ≤ 9 * n := by omega
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hn'R : (22 : ℝ) ≤ n' := by exact_mod_cast hn'
  -- the size of `q`
  have hqv : (q : ℝ) ^ 10 ≤ vC ^ (n' + 1) := by
    refine hnq.le.trans ?_
    calc (10 : ℝ) ^ ((2.9245 : ℝ) * n) ≤ (10 : ℝ) ^ ((2.9245 : ℝ) * 20 / 9 * ((n' + 1 : ℕ) : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (9 : ℝ) * n ≤ 20 * ((n' + 1 : ℕ) : ℝ) := by exact_mod_cast h9.le
          nlinarith
      _ = ((10 : ℝ) ^ ((2.9245 : ℝ) * 20 / 9)) ^ (n' + 1) := Real.rpow_mul_natCast (by norm_num) _ _
      _ ≤ vC ^ (n' + 1) := pow_le_pow_left₀ (by positivity) ten_rpow_le_v _
  -- the analytic hypotheses
  have hr : Real.pi / 2 ≤ (((10 + 1) * (2 * n') : ℕ) : ℝ) + 1 := by
    push_cast; nlinarith
  have hz : (n' : ℝ) * (Real.pi / 2) / (((10 + 1) * (2 * n') : ℕ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    push_cast; nlinarith
  -- the main smallness condition
  have hE : 2 * (Knorm 10 n' : ℝ) * ((2 * q : ℕ) : ℝ) ^ 10 * Eb 10 n' ≤ 1 := by
    have hQ : ((2 * q : ℕ) : ℝ) ^ 10 ≤ 2 ^ 10 * vC ^ (n' + 1) := by
      push_cast; rw [mul_pow]; gcongr
    have hEb := Eb_le n'
    have hEb0 : 0 ≤ Eb 10 n' := by
      unfold Eb
      have : (n' : ℝ) * (Real.pi / 2) / (((10 + 1) * (2 * n') : ℕ) + 1) < 1 := hz
      have : 0 < 1 - (n' : ℝ) * (Real.pi / 2) / (((10 + 1) * (2 * n') : ℕ) + 1) := by linarith
      positivity
    have key : ∀ β : ℝ, 0 ≤ β → (lcmUpTo (2 * n') : ℝ) ≤ β ^ (2 * n') →
        2 * (Knorm 10 n' : ℝ) * ((2 * q : ℕ) : ℝ) ^ 10 * Eb 10 n' ≤ fseq C0f (Bf β) n' := by
      intro β hβ0 hβ
      have hK := Knorm_le n' β hβ
      calc 2 * (Knorm 10 n' : ℝ) * ((2 * q : ℕ) : ℝ) ^ 10 * Eb 10 n'
          ≤ 2 * (((2 * n').factorial : ℝ) ^ 11 * (β ^ 20) ^ n' * 3628800) *
              (2 ^ 10 * vC ^ (n' + 1)) *
              (rhoC ^ (22 * n') / ((22 * n').factorial : ℝ) * cC ^ (22 * n' + 11)) := by
            have hv : 0 ≤ vC := by unfold vC; norm_num
            apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num)) hQ
              (by positivity) (by positivity)) hEb hEb0
            exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (pow_nonneg hv _))
        _ = fseq C0f (Bf β) n' := by
            unfold fseq C0f Bf
            rw [show 22 * n' = 22 * n' by rfl, pow_add, pow_add, pow_mul, pow_mul, mul_pow, mul_pow,
              mul_pow]
            ring
    rcases Nat.lt_or_ge n' 101 with hsmall | hbig
    · refine (key 3 (by norm_num) ?_).trans (fseq3_le_one n' hn')
      have := lcmUpTo_le_three_pow (n := 2 * n') (by omega)
      exact_mod_cast this
    · exact (key 3.49 (by norm_num) (lcmUpTo_le_real _)).trans (fseq349_le_one n' (by omega))
  have hcore := core 10 n' p q hq hpq hr hz hE
  -- the final comparison
  have hTb0 : 0 < Tb 10 n' := by
    unfold Tb Wb
    have := lcmUpTo_pos (2 * n')
    have hs : (∑ s ∈ Finset.range (10 + 1), (s : ℝ) * 2 ^ (s - 1)) = 9217 := by
      norm_num [Finset.sum_range_succ]
    rw [hs]
    have : 0 < ((((10 + 1) * (2 * n') + 10).choose ((10 + 1) * (2 * n')) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    positivity
  set X : ℝ := (10 : ℝ) ^ ((8.9101 : ℝ) * n) with hX
  have hX0 : 0 < X := by positivity
  have hTX : 2 ^ 10 * Tb 10 n' < X := by
    have h1 := two_pow_mul_Tb_le n'
    have h2 := gseq_le_one n' hn'
    have hu : (0 : ℝ) < uC := by unfold uC; norm_num
    have h3 : uC ^ n' ≤ X := by
      calc uC ^ n' ≤ ((10 : ℝ) ^ ((8.9101 : ℝ) * 20 / 9)) ^ n' :=
            pow_le_pow_left₀ hu.le u_le_ten_rpow _
        _ = (10 : ℝ) ^ ((8.9101 : ℝ) * 20 / 9 * (n' : ℝ)) :=
            (Real.rpow_mul_natCast (by norm_num) _ _).symm
        _ ≤ X := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : (20 : ℝ) * n' ≤ 9 * n := by exact_mod_cast h20
            nlinarith
    have h4 : 0 < uC ^ n' := pow_pos hu _
    nlinarith
  have hq0 : (0 : ℝ) < (q : ℝ) ^ 10 := by positivity
  refine lt_of_lt_of_le ?_ hcore
  rw [Real.rpow_neg (by norm_num), ← hX]
  have hQ : ((2 * q : ℕ) : ℝ) ^ 10 = 2 ^ 10 * (q : ℝ) ^ 10 := by push_cast; ring
  have e : X⁻¹ / (q : ℝ) ^ 10 = 1 / (X * (q : ℝ) ^ 10) := by field_simp
  rw [hQ, e]
  apply one_div_lt_one_div_of_lt (by positivity)
  have := mul_lt_mul_of_pos_right hTX hq0
  linarith

end PartFinal
end Component_MahlerReference

/- Source component: PiBoundBridge.lean -/
section Component_PiBoundBridge

set_option autoImplicit false

namespace PiIrrationality

/-- Increasing an upper bound preserves the epsilon formulation. -/
theorem UpperBound.mono {A B : ℝ} (hA : UpperBound A) (hAB : A ≤ B) :
    UpperBound B := by
  intro ε hε
  obtain ⟨Q, hQ⟩ := hA ε hε
  refine ⟨Q, ?_⟩
  intro p q hq hQq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := Real.rpow_le_rpow_of_exponent_le hq1 (show A + ε ≤ B + ε from by linarith)
  exact lt_of_le_of_lt (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hq0 _) hp)
    (hQ p q hq hQq)

/-- An eventual non-strict power lower bound implies the epsilon formulation. -/
theorem upperBound_of_eventual_power_bound {B : ℝ}
    (hB : ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
      1 / (q : ℝ) ^ B ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) :
    UpperBound B := by
  obtain ⟨Q, hQ⟩ := hB
  intro ε hε
  refine ⟨max Q 2, ?_⟩
  intro p q hq hQq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq2 : 2 ≤ q := le_trans (le_max_right Q 2) hQq
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hq2)
  have hp := Real.rpow_lt_rpow_of_exponent_lt hq1 (lt_add_of_pos_right B hε)
  exact lt_of_lt_of_le (one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hq0 _) hp)
    (hQ p q hq (le_trans (le_max_left Q 2) hQq))

/-- It suffices to bound approximations having positive numerator. -/
theorem upperBound_of_eventual_power_bound_pos {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < p → 0 < q → Q ≤ q →
      1 / (q : ℝ) ^ B ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) :
    UpperBound B := by
  apply upperBound_of_eventual_power_bound
  obtain ⟨Q, hQ⟩ := hB
  refine ⟨Q, ?_⟩
  intro p q hq hQq
  by_cases hp : 0 < p
  · exact hQ p q hp hq hQq
  · have hp0 : (p : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hp)
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hrpow : 1 ≤ (q : ℝ) ^ B := Real.one_le_rpow hq1 hB0
    have hfrac : (p : ℝ) / (q : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hp0 hq0.le
    have hrecip : 1 / (q : ℝ) ^ B ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hq0 B)).mpr hrpow
    have habs : 1 ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]
      linarith [Real.two_le_pi]
    exact hrecip.trans habs

/-- For exponent 20, only positive approximations below 3.15 require an estimate. -/
theorem upperBound_twenty_of_eventual_near_power_bound
    (hB : ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < p → 0 < q → Q ≤ q →
      (p : ℝ) / (q : ℝ) < 63 / 20 →
      1 / (q : ℝ) ^ (20 : ℝ) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) :
    UpperBound 20 := by
  apply upperBound_of_eventual_power_bound_pos (by norm_num)
  obtain ⟨Q, hQ⟩ := hB
  refine ⟨max Q 1000, ?_⟩
  intro p q hp hq hQq
  by_cases hnear : (p : ℝ) / (q : ℝ) < 63 / 20
  · exact hQ p q hp hq (le_trans (le_max_left Q 1000) hQq) hnear
  · have hq1000 : (1000 : ℝ) ≤ q := by
      exact_mod_cast (le_trans (le_max_right Q 1000) hQq)
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hpow : (q : ℝ) ≤ (q : ℝ) ^ (20 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ q)
        (by norm_num : (1 : ℝ) ≤ 20)
    have hrecip : 1 / (q : ℝ) ^ (20 : ℝ) ≤ 1 / (1000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (hq1000.trans hpow)
    have hfar : 63 / 20 ≤ (p : ℝ) / (q : ℝ) := le_of_not_gt hnear
    have habs : 1 / (1000 : ℝ) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
      rw [abs_of_nonpos (by linarith [Real.pi_lt_d4])]
      linarith [Real.pi_lt_d4]
    exact hrecip.trans habs

end PiIrrationality
end Component_PiBoundBridge

/- Source component: PntLcm.lean -/
section Component_PntLcm

set_option autoImplicit false
open Filter Asymptotics
open scoped Topology

namespace PiIrrationality

theorem eventual_psi_upper (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + δ) * x := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  have ht : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
    simpa only [neg_mul, Function.comp_def] using tendsto_neg_atTop_atBot.comp (hh.const_mul_atTop hc)
  have he : ∀ᶠ x : ℝ in atTop,
      C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < δ :=
    (show Tendsto (fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) by simpa using ht.const_mul C).eventually_lt_const hδ
  filter_upwards [hbound.bound, he, eventually_ge_atTop (0 : ℝ)] with x hx he hx0
  have hxp := Real.exp_pos (-c * (Real.log x) ^ ((1 : ℝ) / 10))
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
    abs_of_nonneg (mul_nonneg hx0 hxp.le)] at hx
  have hab := le_abs_self (Chebyshev.psi x - x)
  nlinarith

theorem eventual_lcm_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Nat.lcmUpto n : ℝ) ≤ Real.exp ((1 + δ) * n) := by
  have h := tendsto_natCast_atTop_atTop.eventually (eventual_psi_upper δ hδ)
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have hlog := hN n hn
  rw [Chebyshev.psi_eq_log_lcmUpto] at hlog
  have hnpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  simpa only [Real.exp_log hnpos] using Real.exp_le_exp.mpr hlog

end PiIrrationality
end Component_PntLcm

/- Source component: MahlerPnt.lean -/
section Component_MahlerPnt
set_option autoImplicit false

namespace PiMahler

theorem lcmUpTo_eq_lcmUpto (n : ℕ) : lcmUpTo n = Nat.lcmUpto n := by
  apply Nat.dvd_antisymm
  · apply lcmUpTo_dvd
    intro i hi hin
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hi, hin⟩)
  · apply Finset.lcm_dvd
    intro i hi
    exact dvd_lcmUpTo n i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2

theorem eventual_lcmUpTo_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (lcmUpTo n : ℝ) ≤ Real.exp ((1 + δ) * n) := by
  simpa only [lcmUpTo_eq_lcmUpto] using PiIrrationality.eventual_lcm_upper δ hδ

end PiMahler
end Component_MahlerPnt

/- Source component: MahlerPaired.lean -/
section Component_MahlerPaired

set_option autoImplicit false

namespace PiMahler
open Polynomial Complex

lemma mem_nodes_iff (n : ℕ) (j : ℤ) : j ∈ nodes n ↔ -(n : ℤ) ≤ j ∧ j ≤ n := by
  simp only [nodes, Finset.mem_map, Finset.mem_range, nodeEmb_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    omega
  · intro hj
    refine ⟨(j + n).toNat, ?_, ?_⟩
    · omega
    · omega

lemma nodes_zero : nodes 0 = {0} := by
  ext j
  simp only [mem_nodes_iff, Nat.cast_zero, neg_zero, Finset.mem_singleton]
  omega

lemma nodes_succ (n : ℕ) : nodes (n + 1) = insert (-(n + 1 : ℤ)) (insert (n + 1 : ℤ) (nodes n)) := by
  ext j
  simp only [mem_nodes_iff, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
  omega

lemma geom_pair (a : ℚ) : geom a * geom (-a) =
    PowerSeries.expand 2 (by decide) (geom (a ^ 2)) := by
  let D : PowerSeries ℚ := 1 - PowerSeries.C (a ^ 2) * PowerSeries.X ^ 2
  have he : D * PowerSeries.expand 2 (by decide) (geom (a ^ 2)) = 1 := by
    have h := congrArg (PowerSeries.expand 2 (by decide)) (one_sub_mul_geom (a ^ 2))
    simpa [D, map_mul, map_sub, map_one, PowerSeries.expand_X, PowerSeries.expand_C] using h
  have hp : D * (geom a * geom (-a)) = 1 := by
    have hd : D = ((1 - C a * X : ℚ[X]) : PowerSeries ℚ) *
        ((1 - C (-a) * X : ℚ[X]) : PowerSeries ℚ) := by
      simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_X, map_neg]
      dsimp [D]
      simp only [Polynomial.coe_neg, Polynomial.coe_C, map_pow]
      ring
    rw [hd]
    calc _ = (((1 - C a * X : ℚ[X]) : PowerSeries ℚ) * geom a) *
        (((1 - C (-a) * X : ℚ[X]) : PowerSeries ℚ) * geom (-a)) := by ring
      _ = 1 := by rw [one_sub_mul_geom, one_sub_mul_geom, one_mul]
  calc geom a * geom (-a) = (geom a * geom (-a)) * (D * PowerSeries.expand 2 (by decide) (geom (a ^ 2))) := by rw [he, mul_one]
    _ = (D * (geom a * geom (-a))) * PowerSeries.expand 2 (by decide) (geom (a ^ 2)) := by ring
    _ = _ := by rw [hp, one_mul]

lemma geom_zero : geom 0 = 1 := by
  ext k
  cases k <;> simp [geom, PowerSeries.coeff_one]

lemma geom_nodes_product (m n : ℕ) :
    (∏ j ∈ nodes n, geom (j : ℚ) ^ (m + 1)) =
      PowerSeries.expand 2 (by decide)
        (∏ k ∈ Finset.range n, geom (((k + 1 : ℕ) : ℚ) ^ 2) ^ (m + 1)) := by
  induction n with
  | zero => simp [nodes_zero, geom_zero]
  | succ n ih =>
    rw [nodes_succ, Finset.prod_insert, Finset.prod_insert, ih, Finset.prod_range_succ]
    · simp only [map_mul, map_pow, Int.cast_neg, Int.cast_add, Int.cast_natCast,
        Int.cast_one, Nat.cast_add, Nat.cast_one]
      rw [← geom_pair]
      ring
    · rw [mem_nodes_iff]
      omega
    · simp only [Finset.mem_insert, mem_nodes_iff]
      omega

lemma Eser_paired (m n : ℕ) : Eser m (nodes n) =
    PowerSeries.expand 2 (by decide)
      (∏ k ∈ Finset.range n, geom (((k + 1 : ℕ) : ℚ) ^ 2) ^ (m + 1)) := by
  rw [Eser_eq (nodes_nonempty n), geom_nodes_product]

lemma Eser_paired_coeff_odd (m n t : ℕ) :
    PowerSeries.coeff (2 * t + 1) (Eser m (nodes n)) = 0 := by
  rw [Eser_paired]
  exact PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by omega)

lemma Dom.prod_nat {T : Finset ℕ} {f g : ℕ → PowerSeries ℚ}
    (h : ∀ k ∈ T, Dom (f k) (g k)) : Dom (∏ k ∈ T, f k) (∏ k ∈ T, g k) := by
  induction T using Finset.induction_on with
  | empty => simpa using Dom.one
  | @insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma Eser_paired_coeff_bound (m n t : ℕ) (hn : 0 < n) :
    |PowerSeries.coeff (2 * t) (Eser m (nodes n))| ≤
      (((m + 1) * n - 1 + t).choose ((m + 1) * n - 1) : ℚ) * (n : ℚ) ^ (2 * t) := by
  rw [Eser_paired, PowerSeries.coeff_expand_mul]
  have hd : Dom (∏ k ∈ Finset.range n, geom (((k + 1 : ℕ) : ℚ) ^ 2) ^ (m + 1))
      (∏ k ∈ Finset.range n, geom ((n : ℚ) ^ 2) ^ (m + 1)) := by
    apply Dom.prod_nat
    intro k hk
    apply Dom.pow
    apply Dom_geom
    rw [abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  have hpos : 0 < (m + 1) * n := Nat.mul_pos (by omega) hn
  have hh := hd t
  rw [Finset.prod_const, Finset.card_range, ← pow_mul,
    show (m + 1) * n = ((m + 1) * n - 1) + 1 by omega, coeff_geom_pow, ← pow_mul] at hh
  exact hh

lemma tau_shift_eq_coeff (m n h k : ℕ) (hh : h ≤ m) :
    tau m (nodes n) h (k + ((m + 1) * (2 * n) + m - h)) =
      PowerSeries.coeff k (Eser m (nodes n)) := by
  rw [tau_eq_Lam]
  simp only [Eser, PowerSeries.coeff_mk, card_nodes]
  congr 2
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem R_bound_paired (m n' : ℕ) (hn : 0 < n') (h : ℕ) (hh : h ≤ m) (y : ℂ) (r : ℝ) (hy : ‖y‖ ≤ r)
    (hr : r ≤ ((m + 1) * (2 * n') : ℕ) + 1)
    (hz : (n' : ℝ) * r / (((m + 1) * (2 * n') : ℕ) + 1) < 1) :
    ‖∑ i ∈ Finset.range (2 * n' + 1), ∑ s ∈ Finset.range (m + 1),
        (aa m n' h (nodeEmb n' i) s : ℂ) *
          (y ^ s * Complex.exp (((nodeEmb n' i : ℤ) : ℂ) * y))‖ ≤
      r ^ ((m + 1) * (2 * n')) / (((m + 1) * (2 * n')).factorial : ℝ) *
        (1 / (1 - ((n' : ℝ) * r / (((m + 1) * (2 * n') : ℕ) + 1)) ^ 2)) ^ ((m + 1) * n') := by
  set M0 := (m + 1) * (2 * n') with hM0
  set N := M0 + m with hN
  set z : ℝ := (n' : ℝ) * r / ((M0 : ℕ) + 1) with hzdef
  have hr0 : 0 ≤ r := (norm_nonneg y).trans hy
  have hz0 : 0 ≤ z := by positivity
  have hcard : (m + 1) * (nodes n').card - 1 = N := by
    rw [card_nodes, hN, hM0, Nat.mul_succ]; omega
  set c : ℕ → ℂ := fun L => ((tau m (nodes n') h L / (L.factorial : ℚ) : ℚ) : ℂ) * y ^ L with hc
  have hS := R_hasSum m n' h y
  rw [← hasSum_nat_add_iff' (N - h)] at hS
  have hzero : ∑ i ∈ Finset.range (N - h), c i = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    rw [Finset.mem_range] at hL
    rw [hc]
    beta_reduce
    rw [tau_eq_zero (h := h) (l := L) (nodes_nonempty n') (by rw [hcard]; omega)]
    simp
  rw [hzero, sub_zero] at hS
  have hcodd : ∀ k, c (2 * k + 1 + (N - h)) = 0 := by
    intro k
    dsimp only [c]
    rw [tau_shift_eq_coeff m n' h (2 * k + 1) hh,
      Eser_paired_coeff_odd]
    simp
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by intro a b hab; dsimp only at hab; omega
  have heven : HasSum (fun k => c (2 * k + (N - h))) _ :=
    (hinj.hasSum_iff (fun k hk => by
      have hkodd : k = 2 * (k / 2) + 1 := by
        have hhkr : ¬ ∃ a, 2 * a = k := hk
        by_contra hbad
        apply hhkr
        exact ⟨k / 2, by omega⟩
      rw [hkodd]
      exact hcodd (k / 2))).mpr hS
  have hz2 : ‖z ^ 2‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hdpos : 0 < (m + 1) * n' := Nat.mul_pos (by omega) hn
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) ((m + 1) * n' - 1)
    (r := z ^ 2) hz2).mul_left
      (r ^ M0 / (M0.factorial : ℝ))
  rw [show (m + 1) * n' - 1 + 1 = (m + 1) * n' by omega] at hg
  rw [← one_div_pow] at hg
  refine heven.norm_le_of_bounded hg fun k => ?_
  dsimp only [c]
  rw [norm_mul, norm_pow, Complex.norm_ratCast]
  have htau := Eser_paired_coeff_bound m n' k hn
  rw [← tau_shift_eq_coeff m n' h (2 * k) hh] at htau
  have htauR : |(tau m (nodes n') h (2 * k + (N - h)) : ℝ)| ≤
      (((m + 1) * n' - 1 + k).choose ((m + 1) * n' - 1) : ℝ) * (n' : ℝ) ^ (2 * k) := by
    exact_mod_cast htau
  rw [Rat.cast_div, Rat.cast_natCast, abs_div, Nat.abs_cast]
  have hpow : ‖y‖ ^ (2 * k + (N - h)) ≤ r ^ (2 * k + (N - h)) := pow_le_pow_left₀ (norm_nonneg _) hy _
  have hfac := pow_div_factorial_le hr0 M0 (2 * k + (N - h) - M0)
  rw [show M0 + (2 * k + (N - h) - M0) = 2 * k + (N - h) by omega] at hfac
  have hq1 : r / ((M0 : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hr
  have hq2 : (r / ((M0 : ℝ) + 1)) ^ (2 * k + (N - h) - M0) ≤ (r / ((M0 : ℝ) + 1)) ^ (2 * k) :=
    pow_le_pow_of_le_one (by positivity) hq1 (by omega)
  have hzk : z ^ (2 * k) = (n' : ℝ) ^ (2 * k) * (r / ((M0 : ℝ) + 1)) ^ (2 * k) := by
    rw [hzdef, ← mul_pow, mul_div_assoc]
  calc |(tau m (nodes n') h (2 * k + (N - h)) : ℝ)| / ((2 * k + (N - h)).factorial : ℝ) *
        ‖y‖ ^ (2 * k + (N - h))
      ≤ (((m + 1) * n' - 1 + k).choose ((m + 1) * n' - 1) : ℝ) * (n' : ℝ) ^ (2 * k) * (r ^ (2 * k + (N - h)) /
          ((2 * k + (N - h)).factorial : ℝ)) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        apply mul_le_mul htauR _ (by positivity) (by positivity)
        exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ (((m + 1) * n' - 1 + k).choose ((m + 1) * n' - 1) : ℝ) * (n' : ℝ) ^ (2 * k) * (r ^ M0 / (M0.factorial : ℝ) *
          (r / ((M0 : ℝ) + 1)) ^ (2 * k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hfac.trans (mul_le_mul_of_nonneg_left hq2 (by positivity))
    _ = r ^ M0 / (M0.factorial : ℝ) * ((((m + 1) * n' - 1 + k).choose ((m + 1) * n' - 1) : ℕ) * (z ^ 2) ^ k) := by
        rw [← pow_mul, hzk]; ring
    _ = _ := by rw [Nat.add_comm ((m + 1) * n' - 1) k]

noncomputable def EbPaired (m n : ℕ) : ℝ :=
  (Real.pi / 2) ^ ((m + 1) * (2 * n)) / (((m + 1) * (2 * n)).factorial : ℝ) *
    (1 / (1 - ((n : ℝ) * (Real.pi / 2) / (((m + 1) * (2 * n) : ℕ) + 1)) ^ 2)) ^ ((m + 1) * n)

theorem core_paired (m n' : ℕ) (hn : 0 < n') (p q : ℕ) (hq : 0 < q) (hpq : p < 4 * q)
    (hr : Real.pi / 2 ≤ ((m + 1) * (2 * n') : ℕ) + 1)
    (hz : (n' : ℝ) * (Real.pi / 2) / (((m + 1) * (2 * n') : ℕ) + 1) < 1)
    (hE : 2 * (Knorm m n' : ℝ) * ((2 * q : ℕ) : ℝ) ^ m * EbPaired m n' ≤ 1) :
    1 / (((2 * q : ℕ) : ℝ) ^ m * Tb m n') ≤ |Real.pi - (p : ℝ) / q| := by
  set Y : ℂ := (Real.pi / 2 : ℝ) * I with hY
  set y0 : ℂ := (((p : ℝ) / (2 * q) : ℝ) : ℂ) * I with hy0
  obtain ⟨h, hS⟩ := exists_S_ne_zero m n' y0
  have hSy0 : Sfun m n' h y0 ≠ 0 := by
    unfold Sfun Acoef
    rw [← Fin.sum_univ_eq_sum_range (fun s => (∑ i ∈ Finset.range (2 * n' + 1),
      (aa m n' h (nodeEmb n' i) s : ℂ) * Complex.I ^ i) * y0 ^ s)]
    exact hS
  have hh : (h : ℕ) ≤ m := Nat.lt_succ_iff.1 h.2
  set K : ℝ := (Knorm m n' : ℝ) with hK
  have hK0 : 0 < K := by
    rw [hK]; unfold Knorm
    have := lcmUpTo_pos (2 * n')
    positivity
  have hKn : Knorm m n' ≠ 0 := by
    have := hK0; rw [hK] at this; exact_mod_cast this.ne'
  set Q : ℝ := ((2 * q : ℕ) : ℝ) ^ m with hQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  -- lower bound from integrality
  have hlow : 1 ≤ Q * K * ‖Sfun m n' h y0‖ := by
    have hGI := Sfun_GI m n' h p q hq
    have := hGI.one_le_norm (by
      apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by
        have : (0 : ℝ) < 2 * q := by positivity
        exact_mod_cast this.ne')) (Nat.cast_ne_zero.2 hKn)) hSy0)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast] at this
    exact this
  -- analytic upper bound at `Y`
  have hY1 : ‖Sfun m n' h Y‖ ≤ EbPaired m n' := by
    rw [hY, norm_Sfun_eq_Rfun]
    unfold Rfun EbPaired
    apply R_bound_paired m n' hn h hh _ _ _ hr hz
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  -- difference
  have hpi4 := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have hy0n : ‖y0‖ ≤ 2 := by
    rw [hy0, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : (p : ℝ) < 4 * q := by exact_mod_cast hpq
    linarith
  have hYn : ‖Y‖ ≤ 2 := by
    rw [hY, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hdiff := norm_Sfun_sub_le m n' h y0 Y hy0n hYn
  have hyY : ‖y0 - Y‖ = |Real.pi - (p : ℝ) / q| / 2 := by
    rw [hy0, hY, ← sub_mul, ← Complex.ofReal_sub, Complex.norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, show (p : ℝ) / (2 * q) - Real.pi / 2 =
        -((Real.pi - (p : ℝ) / q) / 2) by field_simp; ring, abs_neg, abs_div,
      abs_two]
  have hT : K * (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1))) ≤
      Tb m n' := by
    unfold Tb
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    have hs' : s ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have := norm_K_Acoef_le m n' h s hs' hh
    rw [← hK] at this
    calc K * (‖Acoef m n' h s‖ * (s * 2 ^ (s - 1))) =
        (K * ‖Acoef m n' h s‖) * (s * 2 ^ (s - 1)) := by ring
      _ ≤ Wb m n' * (s * 2 ^ (s - 1)) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  -- combine
  set δ := |Real.pi - (p : ℝ) / q| with hδ
  have htri : ‖Sfun m n' h y0‖ ≤ ‖Sfun m n' h Y‖ +
      ‖Sfun m n' h y0 - Sfun m n' h Y‖ := by
    have := norm_add_le (Sfun m n' h Y) (Sfun m n' h y0 - Sfun m n' h Y)
    simpa using this
  have hE' : Q * K * EbPaired m n' ≤ 1 / 2 := by
    have : 2 * K * Q * EbPaired m n' ≤ 1 := hE
    linarith
  have hEb0 : 0 ≤ EbPaired m n' := (norm_nonneg _).trans hY1
  have key : 1 ≤ 1 / 2 + Q * (Tb m n' * (δ / 2)) := by
    have h1 : Q * K * ‖Sfun m n' h y0‖ ≤ Q * K * EbPaired m n' +
        Q * (K * (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1)))) *
          (δ / 2) := by
      rw [← hyY]
      have := mul_le_mul_of_nonneg_left (htri.trans (add_le_add hY1 hdiff))
        (le_of_lt (mul_pos hQ0 hK0))
      linarith
    have h2 : Q * (K * (∑ s ∈ Finset.range (m + 1), ‖Acoef m n' h s‖ * (s * 2 ^ (s - 1)))) *
        (δ / 2) ≤ Q * (Tb m n' * (δ / 2)) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hQ0.le
      exact mul_le_mul_of_nonneg_right hT (by positivity)
    linarith
  have hTpos : 0 < Q * Tb m n' := by
    by_contra hneg
    push_neg at hneg
    nlinarith [abs_nonneg (Real.pi - (p : ℝ) / q)]
  rw [div_le_iff₀ hTpos]
  nlinarith

end PiMahler
end Component_MahlerPaired

/- Source component: PairedFactorial.lean -/
section Component_PairedFactorial

set_option autoImplicit false

open Filter
namespace PiMahler

noncomputable def pairedFactorialSeq (B : ℝ) (n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ) ^ 6 / ((12 * n).factorial : ℝ) * B ^ n

lemma pairedFactorial_step (B b r : ℝ) (hB : 0 ≤ B) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hBb : B ≤ r * b ^ 12) (n : ℕ) (hn : b * (2 * n + 2) ≤ 12 * n + 1) :
    pairedFactorialSeq B (n + 1) ≤ r * pairedFactorialSeq B n := by
  have hkey : B * ((2 * (n : ℝ) + 1) * (2 * n + 2)) ^ 6 ≤ r * (12 * n + 1) ^ 12 := by
    have hx2 : (2 * (n : ℝ) + 1) * (2 * n + 2) ≤ (2 * n + 2) ^ 2 := by nlinarith
    calc B * ((2 * (n : ℝ) + 1) * (2 * n + 2)) ^ 6
      ≤ (r * b ^ 12) * ((2 * (n : ℝ) + 2) ^ 2) ^ 6 :=
        mul_le_mul hBb (pow_le_pow_left₀ (by positivity) hx2 _) (by positivity) (by positivity)
      _ = r * (b * (2 * n + 2)) ^ 12 := by ring
      _ ≤ r * (12 * n + 1) ^ 12 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn _) hr
  have h2 : ((2 * (n + 1)).factorial : ℝ) = ((2 * n).factorial : ℝ) * ((2 * n + 1) * (2 * n + 2)) := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have h12 := factorial_add_ge (12 * n) 12
  rw [show 12 * n + 12 = 12 * (n + 1) by ring] at h12
  push_cast at h12
  have hG : ((12 * n).factorial : ℝ) * (B * ((2 * (n : ℝ) + 1) * (2 * n + 2)) ^ 6) ≤
      r * ((12 * (n + 1)).factorial : ℝ) := by
    calc _ ≤ ((12 * n).factorial : ℝ) * (r * (12 * n + 1) ^ 12) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = r * (((12 * n).factorial : ℝ) * (12 * n + 1) ^ 12) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h12 hr
  unfold pairedFactorialSeq
  rw [h2]
  simp only [div_mul_eq_mul_div, ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (((2 * n).factorial : ℝ) * ((2 * n + 1) * (2 * n + 2))) ^ 6 * B ^ (n + 1) * ((12 * n).factorial : ℝ)
    = (((2 * n).factorial : ℝ) ^ 6 * B ^ n) *
      (((12 * n).factorial : ℝ) * (B * ((2 * (n : ℝ) + 1) * (2 * n + 2)) ^ 6)) := by ring
    _ ≤ (((2 * n).factorial : ℝ) ^ 6 * B ^ n) * (r * ((12 * (n + 1)).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = _ := by ring

noncomputable def pairedBase : ℝ :=
  (273 / 100) ^ 10 * (1571 / 1000) ^ 12 * (1 / (1 - (1571 / 12000) ^ 2)) ^ 6 * 370

lemma pairedBase_nonneg : 0 ≤ pairedBase := by unfold pairedBase; positivity

lemma pairedBase_le : pairedBase ≤ (99 / 100 : ℝ) * (1199 / 200 : ℝ) ^ 12 := by
  unfold pairedBase
  norm_num

theorem pairedFactorialSeq_tendsto :
    Tendsto (pairedFactorialSeq pairedBase) atTop (nhds 0) := by
  apply Summable.tendsto_atTop_zero
  apply summable_of_ratio_norm_eventually_le (r := (99 / 100 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop (1100 : ℕ)] with n hn
  have hbase := pairedBase_nonneg
  simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ pairedFactorialSeq pairedBase (n+1) by
    unfold pairedFactorialSeq; positivity), abs_of_nonneg (show 0 ≤ pairedFactorialSeq pairedBase n by
    unfold pairedFactorialSeq; positivity)]
  apply pairedFactorial_step pairedBase (1199 / 200) (99 / 100) pairedBase_nonneg
    (by norm_num) (by norm_num) pairedBase_le
  have hnR : (1100 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end PiMahler
end Component_PairedFactorial

/- Source component: PairedNumerics.lean -/
section Component_PairedNumerics
set_option autoImplicit false
open Filter
open scoped Topology
namespace PiMahler

theorem eventual_lcm273 : ∃ N : ℕ, ∀ n ≥ N,
    (lcmUpTo n : ℝ) ≤ (273 / 100 : ℝ)^n := by
  have hlog : 1 < Real.log (273 / 100) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2
      (Real.exp_one_lt_d9.trans (by norm_num))
  obtain ⟨N,hN⟩ := eventual_lcmUpTo_upper (Real.log (273/100)-1) (by linarith)
  refine ⟨N,fun n hn => ?_⟩
  convert hN n hn using 1
  rw [show 1 + (Real.log (273/100)-1) = Real.log (273/100) by ring,
    mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<273/100)]

lemma Knorm_five_le (n : ℕ)
    (hβ : (lcmUpTo (2*n) : ℝ) ≤ (273/100 : ℝ)^(2*n)) :
    (Knorm 5 n : ℝ) ≤ ((2*n).factorial : ℝ)^6 * ((273/100 : ℝ)^10)^n * 120 := by
  unfold Knorm
  push_cast
  have hf : (Nat.factorial 5 : ℝ) = 120 := by norm_num
  rw [hf]
  have hD : (lcmUpTo (2*n) : ℝ)^5 ≤ ((273/100 : ℝ)^10)^n := by
    calc _ ≤ ((273/100 : ℝ)^(2*n))^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hβ _
         _ = _ := by rw [←pow_mul, ←pow_mul]; ring_nf
  gcongr

lemma EbPaired_five_le (n : ℕ) :
    EbPaired 5 n ≤ (1571/1000 : ℝ)^(12*n) / ((12*n).factorial : ℝ) *
      (1/(1-(1571/12000 : ℝ)^2))^(6*n) := by
  unfold EbPaired
  have hrho : Real.pi/2 ≤ (1571/1000 : ℝ) := by linarith [Real.pi_lt_d4]
  have hz : (n : ℝ)*(Real.pi/2)/(((12*n:ℕ):ℝ)+1) ≤ (1571/12000 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hrho (Nat.cast_nonneg n)
    push_cast
    nlinarith
  have hz0 : 0 ≤ (n : ℝ)*(Real.pi/2)/(((12*n:ℕ):ℝ)+1) := by positivity
  have hs : ((n : ℝ)*(Real.pi/2)/(((12*n:ℕ):ℝ)+1))^2 ≤ (1571/12000 : ℝ)^2 :=
    pow_le_pow_left₀ hz0 hz 2
  have hden : 0 < 1 - ((n : ℝ)*(Real.pi/2)/(((12*n:ℕ):ℝ)+1))^2 := by nlinarith
  have hrec : 1/(1-((n : ℝ)*(Real.pi/2)/(((12*n:ℕ):ℝ)+1))^2) ≤
      1/(1-(1571/12000 : ℝ)^2) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  norm_num only at *
  rw [show (5+1)*(2*n)=12*n by ring, show (5+1)*n=6*n by ring]
  exact mul_le_mul (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hrho _) (by positivity))
    (pow_le_pow_left₀ (by positivity) hrec _) (by positivity) (by positivity)

lemma Tb_five_le (n : ℕ)
    (hβ : (lcmUpTo (2*n) : ℝ) ≤ (273/100 : ℝ)^(2*n)) :
    2^5 * Tb 5 n ≤ 4128 * (((n:ℝ)+1)*(12*n+5))^5 *
      ((2:ℝ)^12*(273/100)^10)^n := by
  unfold Tb Wb
  have hs : (∑ s ∈ Finset.range (5+1), (s:ℝ)*2^(s-1)) = 129 := by
    norm_num [Finset.sum_range_succ]
  rw [hs]
  have hD : (lcmUpTo (2*n):ℝ)^5 ≤ ((273/100:ℝ)^10)^n := by
    calc _ ≤ ((273/100:ℝ)^(2*n))^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hβ _
         _ = _ := by rw [←pow_mul,←pow_mul]; ring_nf
  have hC : ((((5+1)*(2*n)+5).choose ((5+1)*(2*n)) : ℕ):ℝ) ≤
      ((12*n:ℝ)+5)^5/120 := by
    rw [Nat.choose_symm_add]
    have hh := Nat.choose_le_pow_div (α:=ℝ) 5 ((5+1)*(2*n)+5)
    norm_num only [Nat.factorial] at hh
    convert hh using 1 <;> norm_num <;> push_cast
    all_goals first | rfl | ring
  have hf : (Nat.factorial 5:ℝ) = 120 := by norm_num
  rw [hf]
  calc _ ≤ (2:ℝ)^5*(129*((2:ℝ)^(2*n*(5+1))*((273/100:ℝ)^10)^n*
      120*((n:ℝ)+1)^5*(((12*n:ℝ)+5)^5/120))) := by gcongr
       _ = _ := by
         rw [show 2*n*(5+1)=12*n by ring, pow_mul]
         simp only [mul_pow]
         ring

theorem eventual_Tb_five : ∃ N:ℕ, ∀ n≥N,
    2^5 * Tb 5 n ≤ (100000000:ℝ)^n := by
  obtain ⟨N,hN⟩ := eventual_lcm273
  have hs := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R:=ℝ) 10
    (r₁ := (2:ℝ)^12*(273/100)^10) (r₂ := 100000000) (by norm_num)
  have he := hs.bound (by norm_num : (0:ℝ) < 1/(4128*34^5))
  rw [Filter.eventually_atTop] at he
  obtain ⟨M,hM⟩ := he
  refine ⟨max 1 (max N M), fun n hn => ?_⟩
  have hn1 : 1≤n := le_trans (le_max_left _ _) hn
  have hnN : N≤n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnM : M≤n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hb := Tb_five_le n (hN (2*n) (by omega))
  have hh := hM n hnM
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤
    (n:ℝ)^10*((2:ℝ)^12*(273/100)^10)^n),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (100000000:ℝ)^n)] at hh
  have hnp : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpoly : (((n:ℝ)+1)*(12*n+5))^5 ≤ 34^5*(n:ℝ)^10 := by
    calc _ ≤ (34*(n:ℝ)^2)^5 := by
           apply pow_le_pow_left₀ (by positivity)
           nlinarith [sq_nonneg ((n:ℝ)-1)]
         _ = _ := by ring
  have hb2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ)≤4128))
    (by positivity : (0:ℝ) ≤ ((2:ℝ)^12*(273/100)^10)^n)
  calc _ ≤ _ := hb.trans hb2
       _ ≤ (100000000:ℝ)^n := by nlinarith

end PiMahler
end Component_PairedNumerics

/- Source component: PairedCoreFinal.lean -/
section Component_PairedCoreFinal
set_option autoImplicit false
open Filter
namespace PiMahler

lemma EbPaired_five_nonneg (n : ℕ) : 0 ≤ EbPaired 5 n := by
  unfold EbPaired
  norm_num only
  apply mul_nonneg (by positivity)
  rw [pow_mul]
  exact pow_nonneg (by positivity) n

theorem eventual_paired_error : ∃ N : ℕ, ∀ n ≥ N,
    (2 : ℝ)^6 * (Knorm 5 n : ℝ) * EbPaired 5 n * (370 : ℝ)^n ≤ 1 := by
  have ht := pairedFactorialSeq_tendsto.const_mul (2^6*120 : ℝ)
  have he : ∀ᶠ n in atTop, (2^6*120 : ℝ)*pairedFactorialSeq pairedBase n ≤ 1 := by
    have hh := ht.eventually (gt_mem_nhds (by norm_num : (2^6*120 : ℝ)*0 < 1))
    filter_upwards [hh] with n hn using le_of_lt hn
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  obtain ⟨N,hN⟩ := eventual_lcm273
  refine ⟨max M N, fun n hn => ?_⟩
  have hK := Knorm_five_le n (hN (2*n) (by omega))
  have hE := EbPaired_five_le n
  have hcomp : (2 : ℝ)^6 * (Knorm 5 n : ℝ) * EbPaired 5 n * (370 : ℝ)^n ≤
      (2^6*120 : ℝ)*pairedFactorialSeq pairedBase n := by
    calc
      _ ≤ (2:ℝ)^6 * (((2*n).factorial:ℝ)^6*((273/100:ℝ)^10)^n*120) *
          ((1571/1000:ℝ)^(12*n)/((12*n).factorial:ℝ) *
            (1/(1-(1571/12000:ℝ)^2))^(6*n)) * (370:ℝ)^n := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul (mul_le_mul_of_nonneg_left hK (by positivity)) hE
                (EbPaired_five_nonneg n) (by positivity)
      _ = _ := by
        unfold pairedFactorialSeq pairedBase
        rw [pow_mul, pow_mul]
        simp only [mul_pow]
        ring
  exact hcomp.trans (hM n (by omega))

theorem eventual_paired_core : ∃ N : ℕ, ∀ n ≥ N, ∀ p q : ℕ,
    0 < p → 0 < q → p < 4*q → (q:ℝ)^5 < (370:ℝ)^n →
    1 / ((q:ℝ)^5 * (100000000:ℝ)^n) ≤ |Real.pi - (p:ℝ)/q| := by
  obtain ⟨N,hN⟩ := eventual_paired_error
  obtain ⟨M,hM⟩ := eventual_Tb_five
  refine ⟨max 1 (max N M), fun n hn p q _hp hq hpq hqn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnM : M ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hEb0 := EbPaired_five_nonneg n
  have hsmall : 2 * (Knorm 5 n : ℝ) * ((2*q:ℕ):ℝ)^5 * EbPaired 5 n ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hqn.le
      (show 0 ≤ (2:ℝ)^6*(Knorm 5 n:ℝ)*EbPaired 5 n by positivity)
    have he := hN n hnN
    push_cast
    nlinarith [hh]
  have hr : Real.pi / 2 ≤ (((5+1)*(2*n):ℕ):ℝ)+1 := by
    have hnR : (1:ℝ)≤n := by exact_mod_cast hn1
    push_cast
    linarith [Real.pi_lt_four]
  have hz : (n:ℝ)*(Real.pi/2)/((((5+1)*(2*n):ℕ):ℝ)+1)<1 := by
    rw [div_lt_one (by positivity)]
    have hp : Real.pi/2 < 2 := by linarith [Real.pi_lt_four]
    have := mul_le_mul_of_nonneg_left hp.le (Nat.cast_nonneg n)
    push_cast
    nlinarith
  have hc := core_paired 5 n (by omega) p q hq hpq hr hz hsmall
  have hTb := hM n hnM
  have hden : 0 < ((2*q:ℕ):ℝ)^5 * Tb 5 n := by
    have hl := lcmUpTo_pos (2*n)
    have hc : 0 < ((5+1)*(2*n)+5).choose ((5+1)*(2*n)) := Nat.choose_pos (by omega)
    unfold Tb Wb
    positivity
  apply le_trans _ hc
  apply one_div_le_one_div_of_le hden
  have hh := mul_le_mul_of_nonneg_left hTb (show 0 ≤ (q:ℝ)^5 by positivity)
  push_cast
  nlinarith [hh]

end PiMahler
end Component_PairedCoreFinal

/- Source component: PairedToBound.lean -/
section Component_PairedToBound

set_option autoImplicit false
open Filter
open scoped Topology

namespace PiIrrationality

lemma paired_numeric_gap : 25 * Real.log (100000000 : ℝ) < 78 * Real.log (370 : ℝ) := by
  have h : (100000000 : ℝ)^25 < (370 : ℝ)^78 := by norm_num
  have hh := Real.strictMonoOn_log (by norm_num) (by norm_num) h
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

lemma paired_eventual_parameter (N : ℕ) :
    ∃ Q : ℕ, ∀ q : ℕ, 0 < q → Q ≤ q →
      ∃ n : ℕ, N ≤ n ∧ (q : ℝ)^5 < (370 : ℝ)^n ∧
        (q : ℝ)^5 * (100000000 : ℝ)^n ≤ (q : ℝ)^(20.6 : ℝ) := by
  let L := Real.log (370 : ℝ)
  let A := Real.log (100000000 : ℝ)
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hA : 0 < A := Real.log_pos (by norm_num)
  have hgap : 0 < (20.6 : ℝ) - (5 + 5*A/L) := by
    have h := paired_numeric_gap
    dsimp [L, A] at *
    have := (div_lt_iff₀ hL).2 (show 5 * Real.log (100000000 : ℝ) < ((20.6 : ℝ) - 5) * Real.log (370 : ℝ) by linarith)
    linarith
  have hev : ∀ᶠ q : ℕ in atTop,
      max ((N : ℝ)*L/5) (A / ((20.6 : ℝ) - (5 + 5*A/L))) ≤ Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  obtain ⟨Q,hQ⟩ := eventually_atTop.1 hev
  refine ⟨Q, fun q hq hQq => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have heq5 : Real.exp (5 * Real.log (q : ℝ)) = (q : ℝ)^5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) from rfl, Real.exp_nat_mul, Real.exp_log hq0]
  have hlog0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hbound := hQ q hQq
  have hN := (le_max_left _ _).trans hbound
  have hB := (le_max_right _ _).trans hbound
  let x := 5 * Real.log (q : ℝ) / L
  let n := Nat.floor x + 1
  have hx0 : 0 ≤ x := div_nonneg (by positivity) hL.le
  have hnlo : x < (n : ℝ) := by simpa [n] using Nat.lt_floor_add_one x
  have hnhi : (n : ℝ) ≤ x + 1 := by
    have := Nat.floor_le hx0
    dsimp [n]
    push_cast
    linarith
  have hNx : (N : ℝ) ≤ x := by
    apply (le_div_iff₀ hL).2
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).1 hN
    linarith
  refine ⟨n, ?_, ?_, ?_⟩
  · exact_mod_cast hNx.trans hnlo.le
  · have hexp : 5 * Real.log (q : ℝ) < (n : ℝ) * L := by
      exact (div_lt_iff₀ hL).1 hnlo
    have he := Real.exp_lt_exp.mpr hexp
    rw [heq5] at he
    simpa [L, Real.exp_nat_mul, Real.exp_log hq0, Real.exp_log (by norm_num : (0 : ℝ) < 370)] using he
  · have hslack := (div_le_iff₀ hgap).1 hB
    have hpow : 5 * Real.log (q : ℝ) + (n : ℝ)*A ≤ (20.6 : ℝ)*Real.log (q : ℝ) := by
      have hnA := mul_le_mul_of_nonneg_right hnhi hA.le
      dsimp [x] at hnA
      have heq : (5 * Real.log (q : ℝ) / L + 1) * A = (5*A/L)*Real.log (q : ℝ) + A := by ring
      rw [heq] at hnA
      nlinarith [hslack]
    have he := Real.exp_le_exp.mpr hpow
    rw [Real.exp_add, heq5] at he
    simpa [A, Real.exp_nat_mul, Real.exp_log hq0,
      Real.exp_log (by norm_num : (0 : ℝ) < 100000000),
      Real.rpow_def_of_pos hq0, mul_comm] using he

lemma upperBound_of_paired_exponential_core
    (hcore : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (p : ℤ) (q : ℕ),
      0 < p → 0 < q → (p : ℝ) < 4 * (q : ℝ) →
      (q : ℝ)^5 < (370 : ℝ)^n →
      1 / ((q : ℝ)^5 * (100000000 : ℝ)^n) ≤ |Real.pi - (p : ℝ)/(q : ℝ)|) :
    UpperBound (20.6 : ℝ) := by
  apply upperBound_of_eventual_power_bound_pos (by norm_num)
  obtain ⟨N, hN⟩ := hcore
  obtain ⟨Q, hQ⟩ := paired_eventual_parameter N
  refine ⟨max Q 2, ?_⟩
  intro p q hp hq hQq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (le_max_right Q 2).trans hQq
  by_cases hnear : (p : ℝ) < 4 * (q : ℝ)
  · obtain ⟨n, hn, hqn, hpow⟩ := hQ q hq ((le_max_left Q 2).trans hQq)
    have hc := hN n hn p q hp hq hnear hqn
    exact (one_div_le_one_div_of_le (by positivity) hpow).trans hc
  · have hfar : 4 ≤ (p : ℝ) / (q : ℝ) :=
      (le_div_iff₀ hq0).2 (le_of_not_gt hnear)
    have hpow : (q : ℝ) ≤ (q : ℝ)^(20.6 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ q)
        (by norm_num : (1 : ℝ) ≤ 20.6)
    have hrecip : 1 / (q : ℝ)^(20.6 : ℝ) ≤ 1/2 :=
      one_div_le_one_div_of_le (by norm_num) (hq2.trans hpow)
    have habs : 1/2 ≤ |Real.pi - (p : ℝ)/(q : ℝ)| := by
      rw [abs_of_nonpos (by linarith [Real.pi_lt_d4])]
      linarith [Real.pi_lt_d4]
    exact hrecip.trans habs

end PiIrrationality
end Component_PairedToBound

theorem solution : PiIrrationality.UpperBound (20.6 : ℝ) := by
  apply PiIrrationality.upperBound_of_paired_exponential_core
  obtain ⟨N, hN⟩ := PiMahler.eventual_paired_core
  refine ⟨N, fun n hn p q hp hq hnear hqn => ?_⟩
  have hp0 : 0 ≤ p := hp.le
  have hcast : (p.toNat : ℝ) = (p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hp0
  have hpNat : 0 < p.toNat := by omega
  have hnearNat : p.toNat < 4*q := by
    exact_mod_cast (show (p.toNat : ℝ) < 4 * (q : ℝ) by simpa only [hcast] using hnear)
  simpa only [hcast] using hN n hn p.toNat q hpNat hq hnearNat hqn

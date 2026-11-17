-- Prove2me | solution 1 for WeierstrassCurve.Phi_PsiSq_no_common_eval_zero_even
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:20.396107+00:00
-- url     : https://prove2.me/submissions/d1039e91-6ed7-42be-9859-97cadceb1d50

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Theorems.Thm_WeierstrassCurve_Psi3_eval_ne_of_Psi2Sq_eval_zero
import Theorems.Thm_WeierstrassCurve_Psi2Sq_eval_ne_of_Psi3_eval_zero
import Theorems.Thm_WeierstrassCurve_prePsi4_eval_ne_of_Psi3_eval_zero
import Definitions.Def_KeystoneResultantCerts
import Theorems.Thm_FLT_EDS_prePsi_adjacent_somos

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_Coprimality` and their helpers. -/

open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

/-- Evaluated adjacent-Somos relation. -/
private lemma eval_preΨ_adjacent_somos
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0) (r : ℤ) :
    pe W x (r - 2) * pe W x (r + 2)
      - (if Even r then 1 else (sx W x) ^ 2) * (pe W x (r - 1) * pe W x (r + 1))
      + c3x W x * (pe W x r) ^ 2 = 0 := by
  have h := prePsi_adjacent_somos W h4 r
  have := congrArg (fun p : k[X] => p.eval x) h
  simp only [pe, sx, c3x, eval_mul, eval_sub, eval_add, eval_pow,
    apply_ite (fun p : k[X] => p.eval x), eval_one] at this ⊢
  linear_combination this

/-- Propagation downward: adjacent zeros `(r, r+1)` force `r-1` to vanish (needs `Ψ₃.eval x ≠ 0`). -/
private lemma preΨ_prev_zero_of_adjacent_zero
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    {r : ℤ} (hc3x : c3x W x ≠ 0)
    (hr : pe W x r = 0) (hr1 : pe W x (r + 1) = 0) :
    pe W x (r - 1) = 0 := by
  have h := eval_preΨ_adjacent_somos W x h4 (r - 1)
  have hsquare : c3x W x * (pe W x (r - 1)) ^ 2 = 0 := by
    have e1 : (r - 1) - 2 = r - 3 := by ring
    have e2 : (r - 1) + 2 = r + 1 := by ring
    have e3 : (r - 1) - 1 = r - 2 := by ring
    have e4 : (r - 1) + 1 = r := by ring
    rw [e1, e2, e3, e4, hr1, hr] at h
    linear_combination h
  have hsq : (pe W x (r - 1)) ^ 2 = 0 := (mul_eq_zero.mp hsquare).resolve_left hc3x
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

/-- Propagation upward: adjacent zeros `(r, r+1)` force `r+2` to vanish (needs `Ψ₃.eval x ≠ 0`). -/
private lemma preΨ_next_zero_of_adjacent_zero
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    {r : ℤ} (hc3x : c3x W x ≠ 0)
    (hr : pe W x r = 0) (hr1 : pe W x (r + 1) = 0) :
    pe W x (r + 2) = 0 := by
  have h := eval_preΨ_adjacent_somos W x h4 (r + 2)
  have hsquare : c3x W x * (pe W x (r + 2)) ^ 2 = 0 := by
    have e1 : (r + 2) - 2 = r := by ring
    have e3 : (r + 2) - 1 = r + 1 := by ring
    have e4 : (r + 2) + 1 = r + 3 := by ring
    rw [e1, e3, e4, hr, hr1] at h
    linear_combination h
  have hsq : (pe W x (r + 2)) ^ 2 = 0 := (mul_eq_zero.mp hsquare).resolve_left hc3x
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

/-- On the `Ψ₃.eval x ≠ 0` stratum, no two adjacent `preΨ` vanish at `x`: the adjacent-zero
pair would propagate (both directions) to index `1`, contradicting `preΨ 1 = 1`. -/
private lemma no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    (hc3x : c3x W x ≠ 0) (r : ℤ) :
    ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0) := by
  rintro ⟨hr, hr1⟩
  have hup : ∀ n, r ≤ n → (pe W x n = 0 ∧ pe W x (n + 1) = 0) := by
    intro n hn
    induction n, hn using Int.le_induction with
    | base => exact ⟨hr, hr1⟩
    | succ m _ ih =>
        refine ⟨ih.2, ?_⟩
        rw [show m + 1 + 1 = m + 2 by ring]
        exact preΨ_next_zero_of_adjacent_zero W x h4 hc3x ih.1 ih.2
  have hdown : ∀ n, n ≤ r → (pe W x n = 0 ∧ pe W x (n + 1) = 0) := by
    intro n hn
    induction n, hn using Int.leInductionDown with
    | base => exact ⟨hr, hr1⟩
    | pred m _ ih =>
        refine ⟨preΨ_prev_zero_of_adjacent_zero W x h4 hc3x ih.1 ih.2, ?_⟩
        rw [show m - 1 + 1 = m by ring]; exact ih.1
  have h1 : pe W x 1 = 0 := by
    rcases le_total r 1 with h | h
    · exact (hup 1 h).1
    · exact (hdown 1 h).1
  rw [pe, preΨ_one, eval_one] at h1
  exact one_ne_zero h1

-- ============ Avenue (c): Ψ₃=0 stratum (rank-3 apparition) + capstone ============

private lemma coeff_left_ne_zero
    (W : WeierstrassCurve k) (x : k)
    (hs2 : sx W x ≠ 0) (m : ℤ) :
    (if Even m then (sx W x)^2 else 1) ≠ 0 := by
  by_cases hm : Even m
  · simp [hm, pow_ne_zero 2 hs2]
  · simp [hm]

private lemma coeff_right_ne_zero
    (W : WeierstrassCurve k) (x : k)
    (hs2 : sx W x ≠ 0) (m : ℤ) :
    (if Even m then 1 else (sx W x)^2) ≠ 0 := by
  by_cases hm : Even m
  · simp [hm]
  · simp [hm, pow_ne_zero 2 hs2]

private lemma eval_preΨ_odd
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    pe W x (2*m + 1)
      = pe W x (m + 2) * (pe W x m)^3 *
          (if Even m then (sx W x)^2 else 1)
        - pe W x (m - 1) * (pe W x (m + 1))^3 *
          (if Even m then 1 else (sx W x)^2) := by
  have h := congrArg (fun p : k[X] => p.eval x) (W.preΨ_odd m)
  simp only [pe, sx, eval_mul, eval_sub, eval_add, eval_pow,
    apply_ite (fun p : k[X] => p.eval x), eval_one] at h ⊢
  linear_combination h

private lemma eval_preΨ_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    pe W x (2*m)
      = (pe W x (m - 1))^2 * pe W x m * pe W x (m + 2)
        - pe W x (m - 2) * pe W x m * (pe W x (m + 1))^2 := by
  have h := congrArg (fun p : k[X] => p.eval x) (W.preΨ_even m)
  simp only [pe, eval_mul, eval_sub, eval_add, eval_pow] at h ⊢
  linear_combination h

/-- Exactly one of `z`, `z-1`, `z+1` is divisible by `3`.  The implication
form is more convenient for the case split below. -/
private lemma mod3_trichotomy (z : ℤ) :
    (3 : ℤ) ∣ z ∨ (3 : ℤ) ∣ z - 1 ∨ (3 : ℤ) ∣ z + 1 := by
  omega

private lemma not_three_dvd_of_three_dvd_sub_one {z : ℤ}
    (h : (3 : ℤ) ∣ z - 1) : ¬ (3 : ℤ) ∣ z := by
  omega

private lemma not_three_dvd_of_three_dvd_add_one {z : ℤ}
    (h : (3 : ℤ) ∣ z + 1) : ¬ (3 : ℤ) ∣ z := by
  omega

private lemma three_dvd_two_mul_add_one_iff_sub_one {m : ℤ} :
    ((3 : ℤ) ∣ 2*m + 1) ↔ (3 : ℤ) ∣ m - 1 := by
  omega

private lemma three_dvd_two_mul_iff {m : ℤ} :
    ((3 : ℤ) ∣ 2*m) ↔ (3 : ℤ) ∣ m := by
  omega

private lemma not_three_dvd_two_mul_add_one_of_three_dvd {m : ℤ}
    (hm : (3 : ℤ) ∣ m) : ¬ (3 : ℤ) ∣ 2*m + 1 := by
  omega

private lemma not_three_dvd_two_mul_add_one_of_three_dvd_add_one {m : ℤ}
    (hm : (3 : ℤ) ∣ m + 1) : ¬ (3 : ℤ) ∣ 2*m + 1 := by
  omega

private lemma not_three_dvd_two_mul_of_three_dvd_sub_one {m : ℤ}
    (hm : (3 : ℤ) ∣ m - 1) : ¬ (3 : ℤ) ∣ 2*m := by
  omega

private lemma not_three_dvd_two_mul_of_three_dvd_add_one {m : ℤ}
    (hm : (3 : ℤ) ∣ m + 1) : ¬ (3 : ℤ) ∣ 2*m := by
  omega

/-- Nat-indexed rank-3 apparition.  This is the actual strong induction. -/
private lemma preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : sx W x ≠ 0)
    (hd4 : pe W x 4 ≠ 0) :
    ∀ N : ℕ, pe W x (N : ℤ) = 0 ↔ (3 : ℤ) ∣ (N : ℤ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N IH =>
    by_cases hsmall : N ≤ 4
    · interval_cases N
      · -- N = 0
        constructor
        · intro _; norm_num
        · intro _
          simpa [pe] using congrArg (fun p : k[X] => p.eval x) (W.preΨ_zero)
      · -- N = 1
        constructor
        · intro h
          have : (1 : k) = 0 := by simpa [pe] using h
          exact (one_ne_zero this).elim
        · intro h
          omega
      · -- N = 2
        constructor
        · intro h
          have : (1 : k) = 0 := by simpa [pe] using h
          exact (one_ne_zero this).elim
        · intro h
          omega
      · -- N = 3
        constructor
        · intro _; norm_num
        · intro _
          simpa [pe] using hc3
      · -- N = 4
        constructor
        · intro h
          exact (hd4 h).elim
        · intro h
          omega
    · have hN5 : 5 ≤ N := by omega
      rcases Nat.even_or_odd N with hEven | hOdd
      · obtain ⟨M, rfl⟩ := even_iff_exists_two_mul.mp hEven
        have hM3 : 3 ≤ M := by omega
        have hMlt : M < 2*M := by omega
        have hMm1lt : M - 1 < 2*M := by omega
        have hMm2lt : M - 2 < 2*M := by omega
        have hMp1lt : M + 1 < 2*M := by omega
        have hMp2lt : M + 2 < 2*M := by omega
        have IHm   := IH M hMlt
        have IHm1  := IH (M - 1) hMm1lt
        have IHm2  := IH (M - 2) hMm2lt
        have IHp1  := IH (M + 1) hMp1lt
        have IHp2  := IH (M + 2) hMp2lt
        have hev := eval_preΨ_even W x (M : ℤ)
        rcases mod3_trichotomy (M : ℤ) with h0 | hrest
        · -- M ≡ 0: the common factor A(M) vanishes.
          have hAm : pe W x (M : ℤ) = 0 := IHm.mpr h0
          have hA : pe W x (2*(M : ℤ)) = 0 := by
            simpa [hAm, mul_assoc, mul_left_comm, mul_comm] using hev
          constructor
          · intro _
            exact three_dvd_two_mul_iff.mpr h0
          · intro _
            exact hA
        · rcases hrest with hm1 | hp1
          · -- M ≡ 1: first summand zero, second summand nonzero.
            have hAm1 : pe W x ((M : ℤ) - 1) = 0 := by
              have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
              simpa [hcast] using (IHm1.mpr (by omega : (3 : ℤ) ∣ ((M - 1 : ℕ) : ℤ)))
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_sub_one hm1 (IHm.mp h)
            have hAm2_ne : pe W x ((M : ℤ) - 2) ≠ 0 := by
              intro h
              have hcast : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by omega
              have hdvd := IHm2.mp (by simpa [hcast] using h)
              omega
            have hAp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
              intro h
              have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
              have hdvd := IHp1.mp (by simpa [hcast] using h)
              omega
            have hsecond_ne :
                pe W x ((M : ℤ) - 2) * pe W x (M : ℤ) *
                    (pe W x ((M : ℤ) + 1))^2 ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hAm2_ne hAm_ne) (pow_ne_zero 2 hAp1_ne)
            have hAne : pe W x (2*(M : ℤ)) ≠ 0 := by
              rw [hev]
              simp [hAm1, hsecond_ne]
            constructor
            · intro h
              exact (hAne h).elim
            · intro hdvd
              exact (not_three_dvd_two_mul_of_three_dvd_sub_one hm1 hdvd).elim
          · -- M ≡ 2: second summand zero, first summand nonzero.
            have hAp1 : pe W x ((M : ℤ) + 1) = 0 := by
              have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
              simpa [hcast] using (IHp1.mpr (by omega : (3 : ℤ) ∣ ((M + 1 : ℕ) : ℤ)))
            have hAm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
              intro h
              have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
              have hdvd := IHm1.mp (by simpa [hcast] using h)
              omega
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_add_one hp1 (IHm.mp h)
            have hAp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
              intro h
              have hcast : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
              have hdvd := IHp2.mp (by simpa [hcast] using h)
              omega
            have hfirst_ne :
                (pe W x ((M : ℤ) - 1))^2 * pe W x (M : ℤ) *
                    pe W x ((M : ℤ) + 2) ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAm1_ne) hAm_ne) hAp2_ne
            have hAne : pe W x (2*(M : ℤ)) ≠ 0 := by
              rw [hev]
              simp [hAp1, hfirst_ne]
            constructor
            · intro h
              exact (hAne h).elim
            · intro hdvd
              exact (not_three_dvd_two_mul_of_three_dvd_add_one hp1 hdvd).elim
      · obtain ⟨M, rfl⟩ := hOdd
        have hM2 : 2 ≤ M := by omega
        have hMlt : M < 2*M + 1 := by omega
        have hMm1lt : M - 1 < 2*M + 1 := by omega
        have hMp1lt : M + 1 < 2*M + 1 := by omega
        have hMp2lt : M + 2 < 2*M + 1 := by omega
        have IHm   := IH M hMlt
        have IHm1  := IH (M - 1) hMm1lt
        have IHp1  := IH (M + 1) hMp1lt
        have IHp2  := IH (M + 2) hMp2lt
        have hodd := eval_preΨ_odd W x (M : ℤ)
        have hcleft := coeff_left_ne_zero W x hs2 (M : ℤ)
        have hcright := coeff_right_ne_zero W x hs2 (M : ℤ)
        rcases mod3_trichotomy (M : ℤ) with h0 | hrest
        · -- M ≡ 0: first summand zero, second summand nonzero.
          have hAm : pe W x (M : ℤ) = 0 := IHm.mpr h0
          have hAm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
            intro h
            have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
            have hdvd := IHm1.mp (by simpa [hcast] using h)
            omega
          have hAp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
            intro h
            have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
            have hdvd := IHp1.mp (by simpa [hcast] using h)
            omega
          have hsecond_ne :
              pe W x ((M : ℤ) - 1) * (pe W x ((M : ℤ) + 1))^3 *
                  (if Even (M : ℤ) then 1 else (sx W x)^2) ≠ 0 := by
            exact mul_ne_zero (mul_ne_zero hAm1_ne (pow_ne_zero 3 hAp1_ne)) hcright
          have hAne : pe W x (2*(M : ℤ) + 1) ≠ 0 := by
            rw [hodd, hAm]
            simpa using hsecond_ne
          constructor
          · intro h
            exact (hAne h).elim
          · intro hdvd
            exact (not_three_dvd_two_mul_add_one_of_three_dvd h0 hdvd).elim
        · rcases hrest with hm1 | hp1
          · -- M ≡ 1: both summands vanish.
            have hAm1 : pe W x ((M : ℤ) - 1) = 0 := by
              have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
              simpa [hcast] using (IHm1.mpr (by omega : (3 : ℤ) ∣ ((M - 1 : ℕ) : ℤ)))
            have hAp2 : pe W x ((M : ℤ) + 2) = 0 := by
              have hcast : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
              simpa [hcast] using (IHp2.mpr (by omega : (3 : ℤ) ∣ ((M + 2 : ℕ) : ℤ)))
            have hA : pe W x (2*(M : ℤ) + 1) = 0 := by
              rw [hodd]
              simp [hAm1, hAp2]
            constructor
            · intro _
              exact three_dvd_two_mul_add_one_iff_sub_one.mpr hm1
            · intro _
              simpa [hA]
          · -- M ≡ 2: second summand zero, first summand nonzero.
            have hAp1 : pe W x ((M : ℤ) + 1) = 0 := by
              have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
              simpa [hcast] using (IHp1.mpr (by omega : (3 : ℤ) ∣ ((M + 1 : ℕ) : ℤ)))
            have hAp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
              intro h
              have hcast : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
              have hdvd := IHp2.mp (by simpa [hcast] using h)
              omega
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_add_one hp1 (IHm.mp h)
            have hfirst_ne :
                pe W x ((M : ℤ) + 2) * (pe W x (M : ℤ))^3 *
                    (if Even (M : ℤ) then (sx W x)^2 else 1) ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hAp2_ne (pow_ne_zero 3 hAm_ne)) hcleft
            have hAne : pe W x (2*(M : ℤ) + 1) ≠ 0 := by
              rw [hodd, hAp1]
              simpa using hfirst_ne
            constructor
            · intro h
              exact (hAne h).elim
            · intro hdvd
              exact (not_three_dvd_two_mul_add_one_of_three_dvd_add_one hp1 hdvd).elim

private lemma preΨ_eval_zero_iff_three_dvd_abs
    (W : WeierstrassCurve k) (x : k)
    (hNat : ∀ N : ℕ, pe W x (N : ℤ) = 0 ↔ (3 : ℤ) ∣ (N : ℤ))
    (n : ℤ) :
    pe W x n = 0 ↔ (3 : ℤ) ∣ n := by
  by_cases hn : 0 ≤ n
  · have hcast : ((Int.toNat n : ℕ) : ℤ) = n := by omega
    simpa [hcast] using hNat (Int.toNat n)
  · have hnle : n ≤ 0 := by omega
    have hpos : 0 ≤ -n := by omega
    have hcast : ((Int.toNat (-n) : ℕ) : ℤ) = -n := by omega
    have hneg_eval : pe W x (-n) = 0 ↔ pe W x n = 0 := by
      have h := congrArg (fun p : k[X] => p.eval x) (W.preΨ_neg n)
      -- `preΨ_neg` has the usual sign, so zero is invariant under negating the index.
      -- Depending on the local theorem orientation, `simpa [pe] using h` or
      -- `simpa [pe, eq_comm] using h` closes this.
      simpa [pe] using h
    have hneg_dvd : ((3 : ℤ) ∣ -n) ↔ (3 : ℤ) ∣ n := by omega
    have hNatNeg := hNat (Int.toNat (-n))
    calc
      pe W x n = 0 ↔ pe W x (-n) = 0 := hneg_eval.symm
      _ ↔ (3 : ℤ) ∣ -n := by simpa [hcast] using hNatNeg
      _ ↔ (3 : ℤ) ∣ n := hneg_dvd

/-- Rank-3 apparition on the `Ψ₃.eval x = 0` stratum. -/
public theorem preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : W.Ψ₂Sq.eval x ≠ 0)
    (hd4 : (W.preΨ 4).eval x ≠ 0)
    (n : ℤ) :
    (W.preΨ n).eval x = 0 ↔ (3 : ℤ) ∣ n := by
  -- `h4` and `[W.IsElliptic]` are kept in the statement for the final caller;
  -- this local rank-3 induction only uses `hc3`, `hs2`, `hd4`, and the recurrences.
  have hNat := preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero
    (W := W) (x := x) hc3 (by simpa [sx] using hs2) (by simpa [pe] using hd4)
  simpa [pe] using preΨ_eval_zero_iff_three_dvd_abs (W := W) (x := x) hNat n

/-- No adjacent vanishing on the `Ψ₃.eval x = 0` stratum. -/
public theorem no_adjacent_preΨ_zero_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : W.Ψ₂Sq.eval x ≠ 0)
    (hd4 : (W.preΨ 4).eval x ≠ 0)
    (r : ℤ) :
    ¬ ((W.preΨ r).eval x = 0 ∧ (W.preΨ (r + 1)).eval x = 0) := by
  intro hz
  have hr : (3 : ℤ) ∣ r :=
    (preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
      (W := W) (x := x) h4 hc3 hs2 hd4 r).mp hz.left
  have hr1 : (3 : ℤ) ∣ r + 1 :=
    (preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
      (W := W) (x := x) h4 hc3 hs2 hd4 (r + 1)).mp hz.right
  omega

/--
Avenue (c) capstone: no two adjacent `preΨ` values vanish at an elliptic
specialization.

If `Ψ₃(x) ≠ 0`, use the already-proved generic adjacent-zero lemma.  If
`Ψ₃(x) = 0`, the resultant certificates supply the two nonzero inputs needed by
the rank-3 apparition lemma.
-/
public theorem no_adjacent_preΨ_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (r : ℤ) :
    ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0) := by
  by_cases hc3 : c3x W x = 0
  · have hs2 : sx W x ≠ 0 :=
      Psi2Sq_eval_ne_of_Psi3_eval_zero (W := W) (x := x) hc3
    have hd4 : (W.preΨ 4).eval x ≠ 0 :=
      prePsi4_eval_ne_of_Psi3_eval_zero (W := W) (x := x) hc3
    exact no_adjacent_preΨ_zero_of_Ψ₃_eval_zero
      (W := W) (x := x) h4 hc3 hs2 hd4 r
  · exact no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
      (W := W) (x := x) h4 hc3 r

/--
At a nonsingular 2-torsion specialization (`Ψ₂Sq(x)=0`), no odd `preΨ_n(x)`
vanishes.

The proof is the promised strong induction on positive odd indices.  It uses
Mathlib's `normEDSRec'` recursion principle for the natural-indexed EDS.  In the
odd recursive branch, the recurrence

```lean
W.preΨ'_odd m
```

collapses after evaluation at `x` because `(W.Ψ₂Sq).eval x = 0`.

* if `Even m`, then
  `preΨ' (2*(m+2)+1) = - preΨ'(m+1) * preΨ'(m+3)^3`;
* if `¬ Even m`, then
  `preΨ' (2*(m+2)+1) = preΨ'(m+4) * preΨ'(m+2)^3`.

The bases are `preΨ_1 = 1` and `preΨ_3 = Ψ₃`, with the latter nonzero by the
resultant certificate `Psi3_eval_ne_of_Psi2Sq_eval_zero`.
-/
public theorem preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (hs : sx W x = 0)
    {n : ℤ} (hn : ¬ Even n) :
    pe W x n ≠ 0 := by
  classical

  have hc3_ne : c3x W x ≠ 0 :=
    Psi3_eval_ne_of_Psi2Sq_eval_zero (W := W) (x := x) hs

  have hNat : ∀ N : ℕ, ¬ Even ((N : ℕ) : ℤ) → pe W x ((N : ℕ) : ℤ) ≠ 0 := by
    intro N
    induction N using normEDSRec' with
    | zero =>
        intro hodd
        exact False.elim <| hodd (by decide)
    | one =>
        intro _
        simp [pe]
    | two =>
        intro hodd
        exact False.elim <| hodd (by decide)
    | three =>
        intro _
        simpa [pe, c3x] using hc3_ne
    | four =>
        intro hodd
        exact False.elim <| hodd (by decide)
    | even m ih =>
        intro hodd
        exfalso
        apply hodd
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (even_two_mul (((m + 3 : ℕ) : ℤ)))
    | odd m ih =>
        intro _hodd_target
        by_cases hm : Even m
        · have hrec :
              pe W x (((2 * (m + 2) + 1 : ℕ) : ℤ))
                = - (pe W x (((m + 1 : ℕ) : ℤ)) *
                      pe W x (((m + 3 : ℕ) : ℤ)) ^ 3) := by
            have h := congrArg (fun p : Polynomial k => p.eval x) (W.preΨ'_odd m)
            simp only [pe, preΨ_ofNat]
            simpa [sx, hs, hm] using h

          have hm1_odd : ¬ Even (((m + 1 : ℕ) : ℤ)) := by
            intro hbad
            rcases hm with ⟨a, ha⟩
            rcases hbad with ⟨b, hb⟩
            omega
          have hm3_odd : ¬ Even (((m + 3 : ℕ) : ℤ)) := by
            intro hbad
            rcases hm with ⟨a, ha⟩
            rcases hbad with ⟨b, hb⟩
            omega

          have hm1_ne : pe W x (((m + 1 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 1) (by omega) hm1_odd
          have hm3_ne : pe W x (((m + 3 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 3) (by omega) hm3_odd

          rw [hrec]
          exact neg_ne_zero.mpr <| mul_ne_zero hm1_ne (pow_ne_zero 3 hm3_ne)

        · have hm_pos : 0 < m := by
            by_contra hpos
            have hm0 : m = 0 := Nat.eq_zero_of_not_pos hpos
            subst m
            exact hm (by decide)

          have hrec :
              pe W x (((2 * (m + 2) + 1 : ℕ) : ℤ))
                = pe W x (((m + 4 : ℕ) : ℤ)) *
                    pe W x (((m + 2 : ℕ) : ℤ)) ^ 3 := by
            have h := congrArg (fun p : Polynomial k => p.eval x) (W.preΨ'_odd m)
            simp only [pe, preΨ_ofNat]
            simpa [sx, hs, hm] using h

          have hm2_odd : ¬ Even (((m + 2 : ℕ) : ℤ)) := by
            intro hbad
            apply hm
            have hm_even_z : Even ((m : ℕ) : ℤ) := by
              rcases hbad with ⟨a, ha⟩
              refine ⟨a - 1, ?_⟩
              omega
            exact_mod_cast hm_even_z
          have hm4_odd : ¬ Even (((m + 4 : ℕ) : ℤ)) := by
            intro hbad
            apply hm
            have hm_even_z : Even ((m : ℕ) : ℤ) := by
              rcases hbad with ⟨a, ha⟩
              refine ⟨a - 2, ?_⟩
              omega
            exact_mod_cast hm_even_z

          have hm2_ne : pe W x (((m + 2 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 2) (by omega) hm2_odd
          have hm4_ne : pe W x (((m + 4 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 4) (by omega) hm4_odd

          rw [hrec]
          exact mul_ne_zero hm4_ne (pow_ne_zero 3 hm2_ne)

  rcases lt_trichotomy n 0 with hn_neg | hn_zero | hn_pos
  · let N : ℕ := Int.toNat (-n)
    have hNcast : ((N : ℕ) : ℤ) = -n := by
      dsimp [N]
      exact Int.toNat_of_nonneg (by omega)
    have hneg_odd : ¬ Even (-n) := by
      intro h
      exact hn (by simpa [even_neg] using h)
    have hNodd : ¬ Even ((N : ℕ) : ℤ) := by
      simpa [hNcast] using hneg_odd
    have hne_neg : pe W x (-n) ≠ 0 := by
      simpa [hNcast] using hNat N hNodd
    intro hn_zero_eval
    apply hne_neg
    have hpre_neg : pe W x (-n) = - pe W x n := by
      simpa [pe] using congrArg (fun p : Polynomial k => p.eval x) (W.preΨ_neg n)
    simp [hpre_neg, hn_zero_eval]
  · subst n
    exact False.elim <| hn (by decide)
  · let N : ℕ := Int.toNat n
    have hNcast : ((N : ℕ) : ℤ) = n := by
      dsimp [N]
      exact Int.toNat_of_nonneg (by omega)
    have hNodd : ¬ Even ((N : ℕ) : ℤ) := by
      simpa [hNcast] using hn
    simpa [hNcast] using hNat N hNodd

-- ===== Even-index no-common-root (avenue-d core part-1) =====

/--
Even `ΨSq` evaluation in the `pe/sx` notation used by the Keystone coprimality
file.

This is just `ΨSq_even` evaluated at `x`, with the large even-recursion factor
identified with `preΨ (2*m)` by `preΨ_even`.
-/
public theorem ΨSq_eval_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    (W.ΨSq (2 * m)).eval x = (pe W x (2 * m)) ^ 2 * sx W x := by
  have hpre :
      ((W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
          - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2).eval x)
        = pe W x (2 * m) := by
    have h := congrArg (fun p : Polynomial k => p.eval x) (W.preΨ_even m)
    simpa [pe] using h.symm

  have hΨ := congrArg (fun p : Polynomial k => p.eval x) (W.ΨSq_even m)
  calc
    (W.ΨSq (2 * m)).eval x
        = (((W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
              - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2) ^ 2
              * W.Ψ₂Sq).eval x) := by
            simpa using hΨ
    _ = ((W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
              - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2).eval x) ^ 2
            * sx W x := by
            simp [sx]
    _ = (pe W x (2 * m)) ^ 2 * sx W x := by
            rw [hpre]

/--
Even `Φ` evaluation in the `pe/sx` notation.

For `n = 2*m`, the trailing factor in the general definition of `Φ` is `1`, not
`Ψ₂Sq`.
-/
public theorem Φ_eval_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    (W.Φ (2 * m)).eval x
      = x * (W.ΨSq (2 * m)).eval x
          - pe W x (2 * m + 1) * pe W x (2 * m - 1) := by
  have hEven : Even (2 * m) := ⟨m, by ring⟩
  simp [WeierstrassCurve.Φ, pe, hEven] <;> ring

/--
Even-index no-common-root theorem for `Φ` and `ΨSq`.

This is the exact even analogue of `Phi_PsiSq_no_common_eval_zero_odd`.
-/
theorem _root_.solution
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (m : ℤ) :
    ¬ ((W.Φ (2 * m)).eval x = 0 ∧ (W.ΨSq (2 * m)).eval x = 0) := by
  rintro ⟨hΦ, hΨ⟩

  have hpe_sx : (pe W x (2 * m)) ^ 2 * sx W x = 0 := by
    have h := hΨ
    rw [ΨSq_eval_even (W := W) (x := x) (m := m)] at h
    exact h

  have hprod : pe W x (2 * m + 1) * pe W x (2 * m - 1) = 0 := by
    have hΦformula := Φ_eval_even (W := W) (x := x) (m := m)
    have hzero :
        (0 : k) = - (pe W x (2 * m + 1) * pe W x (2 * m - 1)) := by
      simpa [hΦ, hΨ] using hΦformula
    exact neg_eq_zero.mp hzero.symm

  by_cases hs : sx W x = 0
  · have hodd_next : ¬ Even (2 * m + 1) := by
      simpa using Int.not_even_two_mul_add_one m
    have hodd_prev : ¬ Even (2 * m - 1) := by
      simpa [show 2 * (m - 1) + 1 = 2 * m - 1 by ring] using
        (Int.not_even_two_mul_add_one (m - 1))

    have hnext_ne : pe W x (2 * m + 1) ≠ 0 :=
      preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
        (W := W) (x := x) (h4 := h4) (hs := hs)
        (n := 2 * m + 1) hodd_next
    have hprev_ne : pe W x (2 * m - 1) ≠ 0 :=
      preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
        (W := W) (x := x) (h4 := h4) (hs := hs)
        (n := 2 * m - 1) hodd_prev

    exact (mul_ne_zero hnext_ne hprev_ne) hprod

  · have hsq : (pe W x (2 * m)) ^ 2 = 0 :=
      (mul_eq_zero.mp hpe_sx).resolve_right hs
    have hpe_even : pe W x (2 * m) = 0 := sq_eq_zero_iff.mp hsq

    rcases mul_eq_zero.mp hprod with hnext | hprev
    · exact (no_adjacent_preΨ_zero
          (W := W) (x := x) (h4 := h4) (r := 2 * m))
        ⟨hpe_even, hnext⟩
    · exact (no_adjacent_preΨ_zero
          (W := W) (x := x) (h4 := h4) (r := 2 * m - 1))
        ⟨hprev, by
          simpa [show (2 * m - 1) + 1 = 2 * m by ring] using hpe_even⟩

end

end WeierstrassCurve

-- Prove2me | solution 1 for QuantumSixJ.scalar_foundations
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T09:21:08.329166+00:00
-- url     : https://prove2.me/submissions/4af181e1-3fc6-46fb-9d20-df024bc0af0e

import Definitions.Def_QuantumSixJScalar

open QuantumSixJ

-- Appendix (A.1): the formal indeterminate is not zero.
theorem QuantumSixJ.q_ne_zero : q ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

open QuantumSixJ
open scoped QuantumSixJ

private lemma positive_numerator_ne (k : ℕ) (hk : k ≠ 0) :
    q ^ (k : ℤ) ≠ q ^ (-(k : ℤ)) := by
  have hq : q ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  intro he
  simp only [zpow_neg, zpow_natCast] at he
  have hh : q ^ (k + k) = 1 := by
    rw [pow_add]
    calc
      q ^ k * q ^ k = (q ^ k)⁻¹ * q ^ k := congrArg (fun z : Scalar => z * q ^ k) he
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero k hq)
  have hp : (Polynomial.X : Polynomial ℚ) ^ (k + k) = 1 :=
    RatFunc.algebraMap_injective ℚ (by simpa [q] using hh)
  have hd := congrArg Polynomial.natDegree hp
  simp at hd
  omega

private lemma numerator_ne (n : ℤ) (hn : n ≠ 0) : q ^ n ≠ q ^ (-n) := by
  cases n with
  | ofNat k => exact positive_numerator_ne k (by intro hk; apply hn; simp [hk])
  | negSucc k =>
    have hp := positive_numerator_ne (k + 1) (by omega)
    simpa [Int.negSucc_eq] using Ne.symm hp

-- Appendix (A.1), for positive and negative integer indices alike.
theorem QuantumSixJ.qInt_ne_zero (n : ℤ) (hn : n ≠ 0) : ⟬n⟭ ≠ 0 := by
  have hd : q - q⁻¹ ≠ 0 := by
    have hp := numerator_ne 1 (by omega)
    simpa using (sub_ne_zero.mpr hp)
  exact div_ne_zero (sub_ne_zero.mpr (numerator_ne n hn)) hd

open QuantumSixJ

theorem QuantumSixJ.q_denominator_ne_zero : q - q⁻¹ ≠ 0 := by
  intro hz
  have hn := qInt_ne_zero 1 (by omega)
  apply hn
  simp [qInt, hz]

open QuantumSixJ
open scoped QuantumSixJ

theorem QuantumSixJ.qFactorial_ne_zero (n : ℤ) (hn : 0 ≤ n) : ⟬n⟭! ≠ 0 := by
  rw [qFactorial, if_neg (not_lt.mpr hn)]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkpos := (Finset.mem_Icc.mp hk).1
  exact qInt_ne_zero k (by omega)

open QuantumSixJ

theorem QuantumSixJ.delta_ne_zero (j : ℤ) (hj : 0 ≤ j) : Δ j ≠ 0 := by
  rw [Δ, if_pos hj]
  exact mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (qInt_ne_zero (j + 1) (by omega))

open QuantumSixJ

theorem QuantumSixJ.theta_ne_zero (a b c : ℤ) (habc : Admissible a b c) : θ a b c ≠ 0 := by
  rw [θ, if_pos habc]
  rcases habc with ⟨ha, hb, hc, hab, hbc, hca, hpar⟩
  dsimp only
  have hs : 0 ≤ (a + b + c) / 2 + 1 := by omega
  have hsa : 0 ≤ (a + b + c) / 2 - a := by omega
  have hsb : 0 ≤ (a + b + c) / 2 - b := by omega
  have hsc : 0 ≤ (a + b + c) / 2 - c := by omega
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (qFactorial_ne_zero _ hs))
      (qFactorial_ne_zero _ hsa)) (qFactorial_ne_zero _ hsb))
      (qFactorial_ne_zero _ hsc))
    (mul_ne_zero (mul_ne_zero (qFactorial_ne_zero _ ha)
      (qFactorial_ne_zero _ hb)) (qFactorial_ne_zero _ hc))

open QuantumSixJ

-- The horizontal norm in the recurrence section, derived from Appendix evaluations.
theorem QuantumSixJ.h_ne_zero (a b c d j : ℤ) (hj : hAdmissible a b c d j) :
    h a b c d j ≠ 0 := by
  rw [h, if_pos hj]
  exact div_ne_zero (mul_ne_zero (theta_ne_zero a d j hj.1)
    (theta_ne_zero b c j hj.2)) (delta_ne_zero j hj.1.2.2.1)

open QuantumSixJ

-- The vertical norm in the recurrence section, derived from Appendix evaluations.
theorem QuantumSixJ.x_ne_zero (a b c d l : ℤ) (hl : vAdmissible a b c d l) :
    x a b c d l ≠ 0 := by
  rw [x, if_pos hl]
  exact div_ne_zero (mul_ne_zero (theta_ne_zero a b l hl.1)
    (theta_ne_zero c d l hl.2)) (delta_ne_zero l hl.1.2.2.1)

open QuantumSixJ
open scoped QuantumSixJ

private lemma factorial_ne_iff (n : ℤ) : ⟬n⟭! ≠ 0 ↔ 0 ≤ n := by
  constructor
  · intro hn
    by_contra hneg
    exact hn (by simp [qFactorial, show n < 0 by omega])
  · exact qFactorial_ne_zero n

theorem QuantumSixJ.tet_summand_support_bounds (a b c d j l S : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) :
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    let m := max (max (A 0) (A 1)) (max (A 2) (A 3))
    let M := min (B 0) (min (B 1) (B 2))
    tetSummand a b c d j l S ≠ 0 ↔ m ≤ S ∧ S ≤ M := by
  dsimp only
  constructor
  · intro hn
    have hd := (div_ne_zero_iff.mp hn).2
    have hA := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1
    have hB := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).2
    have ha0 := (factorial_ne_iff _).mp (hA 0 (Finset.mem_univ _))
    have ha1 := (factorial_ne_iff _).mp (hA 1 (Finset.mem_univ _))
    have ha2 := (factorial_ne_iff _).mp (hA 2 (Finset.mem_univ _))
    have ha3 := (factorial_ne_iff _).mp (hA 3 (Finset.mem_univ _))
    have hb0 := (factorial_ne_iff _).mp (hB 0 (Finset.mem_univ _))
    have hb1 := (factorial_ne_iff _).mp (hB 1 (Finset.mem_univ _))
    have hb2 := (factorial_ne_iff _).mp (hB 2 (Finset.mem_univ _))
    simp only [max_le_iff, le_min_iff]
    omega
  · rintro ⟨hm, hM⟩
    simp only [max_le_iff] at hm
    simp only [le_min_iff] at hM
    have hS : 0 ≤ S + 1 := by
      have ha := hj.1.1
      have hd := hj.1.2.1
      have hj0 := hj.1.2.2.1
      have ha0 : 0 ≤ tetA a b c d j l 0 := by
        dsimp [tetA]
        omega
      omega
    apply div_ne_zero
      (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (qFactorial_ne_zero _ hS))
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply qFactorial_ne_zero
      fin_cases i <;> simp_all [tetA] <;> omega
    · apply Finset.prod_ne_zero_iff.mpr
      intro k _
      apply qFactorial_ne_zero
      fin_cases k <;> simp_all [tetB] <;> omega

open QuantumSixJ

-- Appendix: the exact Racah summation interval lies in the defining coarse interval.
theorem QuantumSixJ.tet_appendix_bounds_within_coarse (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) :
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    let m := max (max (A 0) (A 1)) (max (A 2) (A 3))
    let M := min (B 0) (min (B 1) (B 2))
    0 ≤ m ∧ m ≤ M ∧ M ≤ a + b + c + d + j + l := by
  rcases hj with ⟨haj, hbj⟩
  rcases hl with ⟨hal, hcl⟩
  rcases haj with ⟨ha, hd, hj, had, hda, hjad, hpaj⟩
  rcases hbj with ⟨hb, hc, _, hbc, hcb, hjbc, hpbj⟩
  rcases hal with ⟨_, _, hl, hab, hba, hlab, hpal⟩
  rcases hcl with ⟨_, _, _, hcd, hdc, hlcd, hpcl⟩
  simp only [tetA, tetB, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.head_fin_const,
    max_le_iff, le_min_iff]
  omega


open QuantumSixJ
open scoped QuantumSixJ

theorem solution :
    (q ≠ 0) ∧
    (q - q⁻¹ ≠ 0) ∧
    (∀ n : ℤ, n ≠ 0 → ⟬n⟭ ≠ 0) ∧
    (∀ n : ℤ, 0 ≤ n → ⟬n⟭! ≠ 0) ∧
    (∀ j : ℤ, 0 ≤ j → Δ j ≠ 0) ∧
    (∀ a b c : ℤ, Admissible a b c → θ a b c ≠ 0) ∧
    (∀ a b c d j : ℤ, hAdmissible a b c d j → h a b c d j ≠ 0) ∧
    (∀ a b c d l : ℤ, vAdmissible a b c d l → x a b c d l ≠ 0) ∧
    (∀ a b c d j l S : ℤ, hAdmissible a b c d j → vAdmissible a b c d l →
      let A := tetA a b c d j l
      let B := tetB a b c d j l
      let m := max (max (A 0) (A 1)) (max (A 2) (A 3))
      let M := min (B 0) (min (B 1) (B 2))
      tetSummand a b c d j l S ≠ 0 ↔ m ≤ S ∧ S ≤ M) ∧
    (∀ a b c d j l : ℤ, hAdmissible a b c d j → vAdmissible a b c d l →
      let A := tetA a b c d j l
      let B := tetB a b c d j l
      let m := max (max (A 0) (A 1)) (max (A 2) (A 3))
      let M := min (B 0) (min (B 1) (B 2))
      0 ≤ m ∧ m ≤ M ∧ M ≤ a + b + c + d + j + l) ∧
    (∀ a b c d j k : ℤ, L a b c d j k = L a b c d k j) ∧
    (∀ a b c d j k : ℤ, k ≠ j → k ≠ j - 2 → k ≠ j + 2 → L a b c d j k = 0) ∧
    (∀ a b c d : ℤ, L a b c d 0 0 = 0) := by
  refine ⟨q_ne_zero, q_denominator_ne_zero, qInt_ne_zero, qFactorial_ne_zero,
    delta_ne_zero, theta_ne_zero, h_ne_zero, x_ne_zero,
    tet_summand_support_bounds, tet_appendix_bounds_within_coarse, ?_, ?_, ?_⟩
  · intro a b c d j k
    by_cases he : j = k
    · subst k; rfl
    · simp only [L, if_neg he, if_neg (Ne.symm he)]
      rw [min_comm k j, max_comm k j]
      simp only [or_comm]
  · intro a b c d j k h0 hm hp
    have hrev : j ≠ k + 2 := by omega
    simp [L, Ne.symm h0, hp, hrev]
  · intro a b c d
    simp [L]

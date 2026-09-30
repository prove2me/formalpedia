-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_jet_eliminant_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T23:35:30.321252+00:00
-- url     : https://prove2.me/submissions/6a9db8fc-a99c-4461-a1a9-639f884cda4b

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum

private lemma eliminant_root_power_iff_jets (x : ℂ) (P : Polynomial ℂ) (N : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ N ∣ P ↔
      ∀ k < N, (Polynomial.derivative^[k] P).eval x = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  have h (k : ℕ) : (Polynomial.derivative^[k] P).eval x =
      (k.factorial : ℂ) * (Polynomial.taylor x P).coeff k := by
    rw [← Polynomial.factorial_smul_hasseDeriv]
    simp [Polynomial.taylor_coeff, nsmul_eq_mul]
  simp_rw [h, mul_eq_zero, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    false_or, Polynomial.taylor_apply]

/-- Finite jet vanishing has the sharp minimum degree `N * X.card`. -/
theorem solution
    (X : Finset ℂ) (N : ℕ) (D : ℝ) :
    (∃ P : Polynomial ℂ, P ≠ 0 ∧ (P.natDegree : ℝ) ≤ D ∧
      ∀ x ∈ X, ∀ k < N, (Polynomial.derivative^[k] P).eval x = 0) ↔
      (N : ℝ) * X.card ≤ D := by
  classical
  let M : Polynomial ℂ := ∏ x ∈ X, (Polynomial.X - Polynomial.C x) ^ N
  have hmonic : M.Monic := Polynomial.monic_prod_of_monic _ _
    (fun x _ => (Polynomial.monic_X_sub_C x).pow N)
  have hdegree : M.natDegree = N * X.card := by
    change (∏ x ∈ X, (Polynomial.X - Polynomial.C x) ^ N).natDegree = _
    rw [Polynomial.natDegree_prod_of_monic X _
      (fun x _ => (Polynomial.monic_X_sub_C x).pow N)]
    simp [mul_comm]
  have hdiv (P : Polynomial ℂ)
      (hP : ∀ x ∈ X, ∀ k < N, (Polynomial.derivative^[k] P).eval x = 0) : M ∣ P := by
    refine Finset.prod_dvd_of_coprime (fun x _ y _ hxy => ?_)
      (fun x hx => (eliminant_root_power_iff_jets x P N).mpr (hP x hx))
    exact (Polynomial.pairwise_coprime_X_sub_C (s := fun x : ℂ => x)
      Function.injective_id hxy).pow
  constructor
  · rintro ⟨P, hP, hD, hjets⟩
    have hle := Polynomial.natDegree_le_of_dvd (hdiv P hjets) hP
    rw [hdegree] at hle
    have hle' : (N : ℝ) * X.card ≤ P.natDegree := by exact_mod_cast hle
    exact hle'.trans hD
  · intro hD
    refine ⟨M, hmonic.ne_zero, ?_, ?_⟩
    · rw [hdegree, Nat.cast_mul]
      exact hD
    · intro x hx
      apply (eliminant_root_power_iff_jets x M N).mp
      exact Finset.dvd_prod_of_mem (fun y => (Polynomial.X - Polynomial.C y) ^ N) hx

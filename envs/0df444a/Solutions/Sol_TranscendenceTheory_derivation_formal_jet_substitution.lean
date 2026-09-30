-- Prove2me | solution 1 for TranscendenceTheory.derivation_formal_jet_substitution
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T17:32:09.598957+00:00
-- url     : https://prove2.me/submissions/f6d8219c-1480-4281-8342-8fc166196582

import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped Classical

private lemma derivation_iterate_mul
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) (n : ℕ) (p q : A) :
    D^[n] (p * q) = ∑ ij ∈ Finset.antidiagonal n,
      n.choose ij.1 • (D^[ij.1] p * D^[ij.2] q) := by
  have hm (a b : A) : D (a * b) = a * D b + D a * b := by
    simpa only [smul_eq_mul, mul_comm b] using D.leibniz a b
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => D^[i] p * D^[j] q) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, hm,
      nsmul_add, Finset.sum_add_distrib, add_right_inj]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm]

private lemma divided_jet_mul
    {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) (v : A →ₐ[K] K) (n : ℕ) (p q : A) :
    v (D^[n] (p * q)) / (n.factorial : K) =
      ∑ ij ∈ Finset.antidiagonal n,
        (v (D^[ij.1] p) / (ij.1.factorial : K)) *
          (v (D^[ij.2] q) / (ij.2.factorial : K)) := by
  rw [derivation_iterate_mul, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hn : i + j = n := Finset.mem_antidiagonal.mp hij
  subst n
  simp only [nsmul_eq_mul, map_mul, map_natCast]
  rw [Nat.cast_add_choose]
  have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hij : ((i + j).factorial : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (i + j))
  field_simp

theorem solution
    (K σ : Type*) [Field K] [CharZero K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (v : σ → K)
    (p : MvPolynomial σ K) (n : ℕ) :
    let J : σ → PowerSeries K := fun i => PowerSeries.mk fun k =>
      MvPolynomial.eval v (D^[k] (MvPolynomial.X i)) / (k.factorial : K)
    (n.factorial : K) * PowerSeries.coeff n (MvPolynomial.aeval J p) =
      MvPolynomial.eval v (D^[n] p) := by
  classical
  let J : σ → PowerSeries K := fun i => PowerSeries.mk fun k =>
    MvPolynomial.eval v (D^[k] (MvPolynomial.X i)) / (k.factorial : K)
  have hzero (k : ℕ) : D^[k] 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k hk => rw [Function.iterate_succ_apply', hk, map_zero]
  have h : ∀ q : MvPolynomial σ K, ∀ k : ℕ,
      PowerSeries.coeff k (MvPolynomial.aeval J q) =
        MvPolynomial.eval v (D^[k] q) / (k.factorial : K) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      intro k
      cases k with
      | zero => simp
      | succ k =>
        rw [Function.iterate_succ_apply, MvPolynomial.derivation_C, hzero]
        simp
    | add q r hq hr =>
      intro k
      rw [map_add, map_add, hq, hr, ← add_div]
      have hadd : D^[k] (q + r) = D^[k] q + D^[k] r := by
        simpa only [Module.End.pow_apply] using! (D.toLinearMap ^ k).map_add q r
      rw [hadd, map_add]
    | mul_X q i hq =>
      intro k
      rw [map_mul, MvPolynomial.aeval_X, PowerSeries.coeff_mul]
      simp only [hq, J, PowerSeries.coeff_mk]
      exact (divided_jet_mul D (MvPolynomial.aeval v) k q (MvPolynomial.X i)).symm
  change (n.factorial : K) * PowerSeries.coeff n (MvPolynomial.aeval J p) = _
  rw [h]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

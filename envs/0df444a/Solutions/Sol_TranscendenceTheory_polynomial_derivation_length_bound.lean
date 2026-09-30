-- Prove2me | solution 1 for TranscendenceTheory.polynomial_derivation_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T11:39:14.894773+00:00
-- url     : https://prove2.me/submissions/961494a8-2c9e-4baa-a17d-abd19b21bf49

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring

noncomputable section

open MvPolynomial

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma derivation_length {σ : Type}
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (H : ℕ) (hH : ∀ i, polyLength (D (X i)) ≤ H)
    (p : MvPolynomial σ ℤ) :
    polyLength (D p) ≤ H * p.totalDegree * polyLength p := by
  classical
  have hD : D = mkDerivation ℤ (fun i => D (X i)) := by
    apply derivation_ext
    intro i
    simp
  have hmon (m : σ →₀ ℕ) (a : ℤ) :
      polyLength (D (monomial m a)) ≤ H * (m.sum fun _ k => k) * a.natAbs := by
    rw [hD, mkDerivation_monomial]
    simp only [Finsupp.sum, Finset.smul_sum, smul_eq_mul, ← C_mul',
      ← mul_assoc, C_mul_monomial]
    apply (polyLength_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ m.support, (a.natAbs * m i) * H := by
        apply Finset.sum_le_sum
        intro i _
        apply (polyLength_mul _ _).trans
        simpa only [polyLength_monomial, Int.natAbs_mul, Int.natAbs_natCast] using
          Nat.mul_le_mul_left (a.natAbs * m i) (hH i)
      _ = _ := by simp only [← Finset.sum_mul, ← Finset.mul_sum]; ring
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply (polyLength_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, H * p.totalDegree * (p.coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m hm
      exact (hmon m _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left H
        (le_totalDegree hm)))
    _ = _ := by rw [← Finset.mul_sum]; rfl

private lemma pderiv_degree {σ : Type} (p : MvPolynomial σ ℤ) (i : σ)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, heq⟩ := (pderiv i p).support.exists_mem_eq_sup
    (by simpa using h) (fun m => m.sum fun _ e => e)
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have := mem_support_iff.mp hm
    rw [coeff_pderiv] at this
    exact (mul_ne_zero_iff.mp this).1
  have hle := le_totalDegree (mem_support_iff.mpr hcoeff)
  simpa [totalDegree, heq, Finsupp.sum_add_index'] using hle

private lemma derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (p : MvPolynomial σ ℤ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma derivation_degree {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2) (p : MvPolynomial σ ℤ) :
    (D p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  have hrepr : D = ∑ i, D (X i) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ i, D (X i) * pderiv i p := by
    conv_lhs => rw [hrepr]
    simp [derivation_sum_apply]
  rw [hvalue]
  apply totalDegree_finsetSum_le
  intro i _
  by_cases hi : pderiv i p = 0
  · simp [hi]
  have hp := pderiv_degree p i hi
  have hmul := totalDegree_mul (D (X i)) (pderiv i p)
  have := hD i
  omega


private lemma iterated_length {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (H : ℕ) (hH : ∀ i, polyLength (D (X i)) ≤ H)
    (p : MvPolynomial σ ℤ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
    polyLength (D^[n] p) ≤
      polyLength p * H ^ n * (p.totalDegree + 1).ascFactorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact (derivation_degree D hD _).trans (by omega)
    · apply (derivation_length D H hH _).trans
      calc
        _ ≤ H * (p.totalDegree + 1 + n) *
            (polyLength p * H ^ n * (p.totalDegree + 1).ascFactorial n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left H (by omega)) ih.2
        _ = _ := by rw [Nat.ascFactorial_succ, pow_succ]; ring

/-- Quadratic integer polynomial derivations have factorial-exponential
coefficient-length growth, uniformly in the derivative order. -/
theorem solution {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (H : ℕ) (hHpos : 1 ≤ H)
    (hH : ∀ i, (∑ m ∈ (D (X i)).support, ((D (X i)).coeff m).natAbs) ≤ H)
    (p : MvPolynomial σ ℤ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
    (∑ m ∈ (D^[n] p).support, ((D^[n] p).coeff m).natAbs) ≤
      (∑ m ∈ p.support, (p.coeff m).natAbs) * n.factorial *
        (2 * H) ^ (p.totalDegree + n) := by
  obtain ⟨hdeg, hlen⟩ := iterated_length D hD H hH p n
  refine ⟨hdeg, hlen.trans ?_⟩
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  calc
    _ ≤ polyLength p * H ^ (p.totalDegree + n) *
        (n.factorial * 2 ^ (p.totalDegree + n)) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hHpos (by omega)))
        (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _))
    _ = _ := by rw [mul_pow]; unfold polyLength; ring


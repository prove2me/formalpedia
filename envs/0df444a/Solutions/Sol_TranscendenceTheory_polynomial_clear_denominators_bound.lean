-- Prove2me | solution 1 for TranscendenceTheory.polynomial_clear_denominators_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T11:58:43.473219+00:00
-- url     : https://prove2.me/submissions/64199c07-34c0-4716-8e8b-2ed881eb677c

import Mathlib.Algebra.MvPolynomial.Degrees
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

private lemma polyLength_one {τ : Type} : polyLength (1 : MvPolynomial τ ℤ) = 1 := by
  exact polyLength_monomial (0 : τ →₀ ℕ) 1

private lemma polyLength_C {τ : Type} (a : ℤ) :
    polyLength (C a : MvPolynomial τ ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_pow {τ : Type} (p : MvPolynomial τ ℤ) (n : ℕ) :
    polyLength (p ^ n) ≤ polyLength p ^ n := by
  induction n with
  | zero => simp [polyLength_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma polyLength_prod {τ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial τ ℤ) :
    polyLength (∏ i ∈ s, f i) ≤ ∏ i ∈ s, polyLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyLength_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_left _ ih)

/-- Clear separate coordinate denominators with degree and coefficient-length bounds. -/
theorem solution {σ τ A : Type} [Fintype σ] [CommRing A]
    (p : MvPolynomial σ ℤ) (k d H : σ → ℕ)
    (s q : σ → MvPolynomial τ ℤ)
    (hp : ∀ i, p.degreeOf i ≤ k i)
    (hs_degree : ∀ i, (s i).totalDegree ≤ d i)
    (hq_degree : ∀ i, (q i).totalDegree ≤ d i)
    (hs_length : ∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ H i)
    (hq_length : ∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ H i) :
    ∃ r : MvPolynomial τ ℤ,
      r.totalDegree ≤ ∑ i, k i * d i ∧
      (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
        (∑ m ∈ p.support, (p.coeff m).natAbs) * ∏ i, H i ^ k i ∧
      ∀ (φ : MvPolynomial τ ℤ →+* A) (y : σ → A),
        (∀ i, φ (s i) = φ (q i) * y i) →
        φ r = (∏ i, φ (q i) ^ k i) * eval₂ (Int.castRingHom A) y p := by
  classical
  let term (m : σ →₀ ℕ) : MvPolynomial τ ℤ :=
    C (p.coeff m) * ∏ i, q i ^ (k i - m i) * s i ^ m i
  let r : MvPolynomial τ ℤ := ∑ m ∈ p.support, term m
  have hm (m : σ →₀ ℕ) (hmem : m ∈ p.support) (i : σ) : m i ≤ k i :=
    (monomial_le_degreeOf i hmem).trans (hp i)
  have hterm_degree (m : σ →₀ ℕ) (hmem : m ∈ p.support) :
      (term m).totalDegree ≤ ∑ i, k i * d i := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ (k i - m i) * (q i).totalDegree + m i * (s i).totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_pow _ _) (totalDegree_pow _ _))
      _ ≤ (k i - m i) * d i + m i * d i :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (hq_degree i))
          (Nat.mul_le_mul_left _ (hs_degree i))
      _ = k i * d i := by rw [← Nat.add_mul, Nat.sub_add_cancel (hm m hmem i)]
  have hterm_length (m : σ →₀ ℕ) (hmem : m ∈ p.support) :
      polyLength (term m) ≤ (p.coeff m).natAbs * ∏ i, H i ^ k i := by
    apply (polyLength_mul _ _).trans
    rw [polyLength_C]
    apply Nat.mul_le_mul_left
    apply (polyLength_prod _ _).trans
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i _
    calc
      _ ≤ polyLength (q i) ^ (k i - m i) * polyLength (s i) ^ m i :=
        (polyLength_mul _ _).trans (Nat.mul_le_mul (polyLength_pow _ _) (polyLength_pow _ _))
      _ ≤ H i ^ (k i - m i) * H i ^ m i :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hq_length i) _) (Nat.pow_le_pow_left (hs_length i) _)
      _ = H i ^ k i := by rw [← pow_add, Nat.sub_add_cancel (hm m hmem i)]
  refine ⟨r, totalDegree_finsetSum_le hterm_degree, ?_, ?_⟩
  · change polyLength r ≤ polyLength p * _
    apply (polyLength_sum_le _ _).trans
    calc
      _ ≤ ∑ m ∈ p.support, (p.coeff m).natAbs * ∏ i, H i ^ k i :=
        Finset.sum_le_sum hterm_length
      _ = _ := by rw [← Finset.sum_mul]; rfl
  · intro φ y hy
    change φ (∑ m ∈ p.support, term m) = _
    rw [map_sum, eval₂_eq']
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hmem
    have hfactor (i : σ) :
        φ (q i) ^ (k i - m i) * φ (s i) ^ m i = φ (q i) ^ k i * y i ^ m i := by
      rw [hy i, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hm m hmem i)]
    simp only [term, map_mul, map_prod, map_pow]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib]
    have hc : φ (C (p.coeff m)) = (Int.castRingHom A) (p.coeff m) := by
      simp
    rw [hc]
    ring


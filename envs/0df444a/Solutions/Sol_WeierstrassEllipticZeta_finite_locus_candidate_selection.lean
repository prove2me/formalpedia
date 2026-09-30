-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_locus_candidate_selection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T06:29:23.379822+00:00
-- url     : https://prove2.me/submissions/92976f67-da65-4f34-a583-e78da6556f83

import Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private def restrictionPoly (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1, T, Polynomial.C (S 0 b), Polynomial.C (S 1 b), Polynomial.C (S 2 b),
      Polynomial.C (S 3 b) + U * Polynomial.C (S 0 b),
      Polynomial.C (S 4 b) + U * Polynomial.C (S 2 b)] Q

private lemma substitution_degree (H : Fin 7 → Polynomial ℂ) (w : Fin 7 → ℕ)
    (hH : ∀ i, (H i).natDegree ≤ w i) (Q : MvPolynomial (Fin 7) ℂ)
    (N : ℕ) (hQ : ∀ d ∈ Q.support, ∑ i : Fin 7, d i * w i ≤ N) :
    (MvPolynomial.eval₂Hom Polynomial.C H Q).natDegree ≤ N := by
  rw [Q.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  calc
    _ ≤ (∏ i : Fin 7, H i ^ d i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i : Fin 7, (H i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i : Fin 7, d i * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hH i))
    _ ≤ N := hQ d hd

private lemma restriction_degree (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (restrictionPoly S b T U Q).natDegree ≤ m * T.natDegree + n * U.natDegree := by
  refine substitution_degree _ ![0, T.natDegree, 0, 0, 0, U.natDegree, U.natDegree] ?_ Q _ ?_
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]
    · simp
    · exact le_rfl
    · simp
    · simp
    · simp
    · exact Polynomial.natDegree_add_le_of_degree_le (by simp)
        (Polynomial.natDegree_mul_C_le _ _)
    · exact Polynomial.natDegree_add_le_of_degree_le (by simp)
        (Polynomial.natDegree_mul_C_le _ _)
  · intro d hd
    obtain ⟨hm, hn⟩ := hQ d hd
    calc
      _ = d 1 * T.natDegree + (d 5 + d 6) * U.natDegree := by
        simp [Fin.sum_univ_succ]
        ring
      _ ≤ m * T.natDegree + n * U.natDegree :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
          (Nat.mul_le_mul_right _ (by omega))

private lemma restriction_eval (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (s : ℂ) :
    (restrictionPoly S b T U Q).eval s =
      MvPolynomial.eval ![1, T.eval s, S 0 b, S 1 b, S 2 b,
        S 3 b + U.eval s * S 0 b, S 4 b + U.eval s * S 2 b] Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [restrictionPoly]
  | add P Q hP hQ => simp_all [restrictionPoly, map_add]
  | mul_X P i hP =>
    simp only [restrictionPoly, map_mul, MvPolynomial.eval₂Hom_X] at *
    rw [Polynomial.eval_mul, hP]
    congr 1
    fin_cases i <;> simp

private lemma polynomial_zero_from_range (p : Polynomial ℂ) (N : ℕ)
    (hp : p.natDegree ≤ N) (hz : ∀ j ∈ Finset.range (N + 1), p.eval (j : ℂ) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun j : Fin (N + 1) => (j.val : ℂ))
  · intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  · intro j
    exact hz j.val (Finset.mem_range.mpr j.isLt)
  · simpa using Nat.lt_succ_of_le hp

private def locusValue (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (w : Fin 3 → ℂ) : ℂ :=
  MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
    S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q

private lemma linear_degree (a b : ℂ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))

private lemma line_restriction (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ) (α : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m + n ∧
      ∀ s : ℂ, p.eval s = locusValue S Q (r + ![s, 0, α * s]) := by
  let T : Polynomial ℂ := Polynomial.C (r 0) + Polynomial.C 1 * Polynomial.X
  let U : Polynomial ℂ := Polynomial.C (r 2) + Polynomial.C α * Polynomial.X
  refine ⟨restrictionPoly S (r 1) T U Q, ?_, ?_⟩
  · exact (restriction_degree S (r 1) T U Q m n hQ).trans (by
      calc
        _ ≤ m * 1 + n * 1 := Nat.add_le_add
          (Nat.mul_le_mul_left _ (linear_degree _ _))
          (Nat.mul_le_mul_left _ (linear_degree _ _))
        _ = _ := by simp)
  · intro s
    simpa [T, U, locusValue] using restriction_eval S (r 1) T U Q s

theorem candidatePeriod_ne_zero (Λ : Submodule ℤ ℂ) (X : Finset ℂ)
    (p : ↥(periodPairCandidates Λ X)) : (candidatePeriod Λ X p : ℂ) ≠ 0 := by
  have h := Finset.mem_offDiag.mp (Finset.mem_filter.mp p.property).1
  exact sub_ne_zero.mpr h.2.2

theorem finite_locus_candidate_card_bound (Λ : Submodule ℤ ℂ) (X : Finset ℂ) :
    Fintype.card (FiniteLocusCandidate Λ X) ≤ 2 + X.card * (X.card - 1) := by
  have h : (periodPairCandidates Λ X).card ≤ X.offDiag.card :=
    Finset.card_filter_le _ _
  have h' : (periodPairCandidates Λ X).card ≤ X.card * (X.card - 1) := by
    simpa [Nat.mul_sub_left_distrib] using h
  simp only [FiniteLocusCandidate, Fintype.card_sum, Fintype.card_unit, Fintype.card_coe]
  omega

theorem resonant_period_mem_iff (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (α z : ℂ) :
    z ∈ resonantPeriods Λ η α ↔ ∃ hz : z ∈ Λ, η ⟨z, hz⟩ = α * z := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.property, ?_⟩
    simpa [LinearMap.mem_ker, sub_eq_zero] using hw
  · rintro ⟨hz, he⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    simpa [LinearMap.mem_ker, sub_eq_zero] using he

theorem collision_determines_candidate (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (α : ℂ) (x y : ℂ) (hx : x ∈ X) (hy : y ∈ X)
    (hne : x ≠ y)
    (heq : (resonantPeriods Λ η α).mkQ x = (resonantPeriods Λ η α).mkQ y) :
    ∃ p : ↥(periodPairCandidates Λ X),
      candidateLocusShape Λ η X (.inr (.inr p)) = .line α := by
  have hmem : x - y ∈ resonantPeriods Λ η α := by
    have hzero : (resonantPeriods Λ η α).mkQ (x - y) = 0 := by
      rw [map_sub, heq, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).mp hzero
  obtain ⟨hΛ, hη⟩ := (resonant_period_mem_iff Λ η α (x - y)).mp hmem
  let p : ↥(periodPairCandidates Λ X) :=
    ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, hΛ⟩⟩
  refine ⟨p, ?_⟩
  change ElementaryLocusShape.line (η ⟨x - y, hΛ⟩ / (x - y)) = .line α
  congr 1
  rw [hη, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hne)]

private theorem scaled_line_samples_iff
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (r : Fin 3 → ℂ) (δ ξ : ℂ) (hδ : δ ≠ 0) :
    (∀ j ∈ Finset.range (m + n + 1),
      locusValue S Q (r + ![(j : ℂ) * δ, 0, (j : ℂ) * ξ]) = 0) ↔
    (∀ w ∈ elementaryLocusSamples (.line (ξ / δ)) r m n,
      locusValue S Q w = 0) := by
  obtain ⟨p, hp, hev⟩ := line_restriction S Q m n hQ r (ξ / δ)
  have hmul (s : ℂ) : (ξ / δ) * (s * δ) = s * ξ := by field_simp
  constructor
  · intro hz
    have hp0 : p = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
        (f := fun j : Fin (m + n + 1) => (j.val : ℂ) * δ)
      · intro i j hij
        exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hδ hij))
      · intro j
        rw [hev, hmul]
        exact hz j.val (Finset.mem_range.mpr j.isLt)
      · simpa using Nat.lt_succ_of_le hp
    rintro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    rw [← hev, hp0, Polynomial.eval_zero]
  · intro hz
    have hp0 : p = 0 := polynomial_zero_from_range p (m + n) hp (by
      intro j hj
      rw [hev]
      exact hz _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    intro j hj
    rw [← hmul, ← hev, hp0, Polynomial.eval_zero]

theorem candidate_locus_samples_iff
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (k : FiniteLocusCandidate Λ X) (r : Fin 3 → ℂ) :
    (∀ w ∈ candidateLocusSamples Λ η X k r m n, locusValue S Q w = 0) ↔
    (∀ w ∈ elementaryLocusSamples (candidateLocusShape Λ η X k) r m n,
      locusValue S Q w = 0) := by
  rcases k with u | u | p
  · rfl
  · rfl
  · simp only [candidateLocusSamples, Finset.forall_mem_image, candidateLocusShape]
    exact scaled_line_samples_iff S Q m n hQ r _ _ (candidatePeriod_ne_zero Λ X p)


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    Fintype.card (FiniteLocusCandidate Λ X) ≤ 2 + X.card * (X.card - 1) ∧
    (∀ (k : FiniteLocusCandidate Λ X) (r : Fin 3 → ℂ),
      (∀ w ∈ candidateLocusSamples Λ η X k r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ↔
      (∀ w ∈ elementaryLocusSamples (candidateLocusShape Λ η X k) r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0)) ∧
    ∀ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
      (∀ w ∈ elementaryLocusSamples shape r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) →
      ∃ k : FiniteLocusCandidate Λ X,
        (∀ w ∈ candidateLocusSamples Λ η X k r m n,
          MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
            S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
        (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X k)).mkQ).card =
          (X.image (elementaryPeriodKernel Λ η shape).mkQ).card ∧
        elementaryDegree shape m ≤ elementaryDegree (candidateLocusShape Λ η X k) m := by
  refine ⟨finite_locus_candidate_card_bound Λ X,
    candidate_locus_samples_iff Λ η X S Q m n hQ, ?_⟩
  intro shape r hz
  cases shape with
  | point => exact ⟨.inl (), hz, rfl, le_rfl⟩
  | fibre => exact ⟨.inr (.inl ()), hz, rfl, le_rfl⟩
  | line α =>
    by_cases hcoll : ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧
        (resonantPeriods Λ η α).mkQ x = (resonantPeriods Λ η α).mkQ y
    · obtain ⟨x, hx, y, hy, hne, heq⟩ := hcoll
      obtain ⟨p, hp⟩ := collision_determines_candidate Λ η X α x y hx hy hne heq
      refine ⟨.inr (.inr p), ?_, ?_, ?_⟩
      · apply (candidate_locus_samples_iff Λ η X S Q m n hQ _ r).mpr
        simpa only [hp, locusValue] using hz
      · rw [hp]
      · rw [hp]
    · have hcard : (X.image (resonantPeriods Λ η α).mkQ).card = X.card := by
        apply Finset.card_image_of_injOn
        intro x hx y hy heq
        by_contra hne
        exact hcoll ⟨x, hx, y, hy, hne, heq⟩
      have hpoint : (X.image (⊥ : Submodule ℤ ℂ).mkQ).card = X.card := by
        apply Finset.card_image_of_injective
        intro x y hxy
        apply sub_eq_zero.mp
        have hzero : (⊥ : Submodule ℤ ℂ).mkQ (x - y) = 0 := by
          rw [map_sub, hxy, sub_self]
        exact (Submodule.Quotient.mk_eq_zero _).mp hzero
      have hr : locusValue S Q r = 0 := by
        have h := hz (r + ![(0 : ℂ), 0, α * 0])
          (Finset.mem_image.mpr ⟨0, by simp, by simp⟩)
        simpa [locusValue] using h
      refine ⟨.inl (), ?_, ?_, ?_⟩
      · simpa [candidateLocusSamples, locusValue] using hr
      · exact hpoint.trans hcard.symm
      · exact Nat.zero_le _

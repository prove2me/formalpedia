-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_elementary_locus_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T16:35:20.250993+00:00
-- url     : https://prove2.me/submissions/4f7ed657-2a3f-4b36-b45f-2177a49b1e34

import Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
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

private lemma horizontal_restriction (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ) (b : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧
      ∀ s : ℂ, p.eval s = locusValue S Q (r + ![s, 0, b]) := by
  let T : Polynomial ℂ := Polynomial.C (r 0) + Polynomial.C 1 * Polynomial.X
  let U : Polynomial ℂ := Polynomial.C (r 2 + b)
  refine ⟨restrictionPoly S (r 1) T U Q, ?_, ?_⟩
  · have hd := restriction_degree S (r 1) T U Q m n hQ
    simp only [U, Polynomial.natDegree_C, mul_zero, add_zero] at hd
    exact hd.trans ((Nat.mul_le_mul_left m (linear_degree (r 0) 1)).trans_eq (Nat.mul_one m))
  · intro s
    simpa [T, U, locusValue] using restriction_eval S (r 1) T U Q s

private lemma vertical_restriction (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ) (a : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧
      ∀ s : ℂ, p.eval s = locusValue S Q (r + ![a, 0, s]) := by
  let T : Polynomial ℂ := Polynomial.C (r 0 + a)
  let U : Polynomial ℂ := Polynomial.C (r 2) + Polynomial.C 1 * Polynomial.X
  refine ⟨restrictionPoly S (r 1) T U Q, ?_, ?_⟩
  · have hd := restriction_degree S (r 1) T U Q m n hQ
    simp only [T, Polynomial.natDegree_C, mul_zero, zero_add] at hd
    exact hd.trans ((Nat.mul_le_mul_left n (linear_degree (r 2) 1)).trans_eq (Nat.mul_one n))
  · intro s
    simpa [T, U, locusValue] using restriction_eval S (r 1) T U Q s

private lemma samples_subset (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) (m n : ℕ) :
    ↑(elementaryLocusSamples shape r m n) ⊆ elementaryLocus shape r := by
  cases shape with
  | point =>
    intro w hw
    have hw' : w = r := by simpa [elementaryLocusSamples] using hw
    subst w
    exact ⟨0, (elementaryDirections .point).zero_mem, add_zero r⟩
  | line α =>
    rintro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨![(j : ℂ), 0, α * (j : ℂ)], ?_, rfl⟩
    simp [elementaryDirections]
  | fibre =>
    rintro w hw
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨![(ij.1 : ℂ), 0, (ij.2 : ℂ)], by simp [elementaryDirections], rfl⟩

private lemma samples_card (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) (m n : ℕ) :
    (elementaryLocusSamples shape r m n).card =
      match shape with
      | .point => 1
      | .line _ => m + n + 1
      | .fibre => (m + 1) * (n + 1) := by
  cases shape with
  | point => simp [elementaryLocusSamples]
  | line α =>
    have hinj : Function.Injective (fun j : ℕ => r + ![(j : ℂ), 0, α * (j : ℂ)]) := by
      intro i j hij
      have h := congrArg (fun v : Fin 3 → ℂ => v 0) hij
      simpa using h
    dsimp only [elementaryLocusSamples]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  | fibre =>
    have hinj : Function.Injective (fun ij : ℕ × ℕ =>
        r + ![(ij.1 : ℂ), 0, (ij.2 : ℂ)]) := by
      intro i j hij
      apply Prod.ext
      · have h := congrArg (fun v : Fin 3 → ℂ => v 0) hij
        simpa using h
      · have h := congrArg (fun v : Fin 3 → ℂ => v 2) hij
        simpa using h
    dsimp only [elementaryLocusSamples]
    rw [Finset.card_image_of_injective _ hinj, Finset.product_eq_sprod, Finset.card_product,
      Finset.card_range, Finset.card_range]

private lemma line_from_samples (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ) (α : ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples (.line α) r m n, locusValue S Q w = 0) :
    ∀ w ∈ elementaryLocus (.line α) r, locusValue S Q w = 0 := by
  obtain ⟨p, hp, heval⟩ := line_restriction S Q m n hQ r α
  have hp0 : p = 0 := polynomial_zero_from_range p (m + n) hp (by
    intro j hj
    rw [heval]
    exact hz _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  rintro w ⟨v, hv, rfl⟩
  have hv' : v 1 = 0 ∧ v 2 = α * v 0 := by
    simpa [elementaryDirections, sub_eq_zero] using hv
  have heq : v = ![v 0, 0, α * v 0] := by
    ext i
    fin_cases i <;> simp [hv'.1, hv'.2]
  rw [heq, ← heval, hp0]
  simp

private lemma fibre_from_samples (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples .fibre r m n, locusValue S Q w = 0) :
    ∀ w ∈ elementaryLocus .fibre r, locusValue S Q w = 0 := by
  have hrows (b : ℕ) (hb : b ∈ Finset.range (n + 1)) (s : ℂ) :
      locusValue S Q (r + ![s, 0, (b : ℂ)]) = 0 := by
    obtain ⟨p, hp, heval⟩ := horizontal_restriction S Q m n hQ r b
    have hp0 : p = 0 := polynomial_zero_from_range p m hp (by
      intro j hj
      rw [heval]
      exact hz _ (Finset.mem_image.mpr ⟨(j, b), Finset.mem_product.mpr ⟨hj, hb⟩, rfl⟩))
    rw [← heval, hp0]
    simp
  have hall (s b : ℂ) : locusValue S Q (r + ![s, 0, b]) = 0 := by
    obtain ⟨p, hp, heval⟩ := vertical_restriction S Q m n hQ r s
    have hp0 : p = 0 := polynomial_zero_from_range p n hp (by
      intro j hj
      rw [heval]
      exact hrows j hj s)
    rw [← heval, hp0]
    simp
  rintro w ⟨v, hv, rfl⟩
  have hv1 : v 1 = 0 := hv
  have heq : v = ![v 0, 0, v 2] := by
    ext i
    fin_cases i <;> simp [hv1]
  rw [heq]
  exact hall _ _


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    ∀ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
      ↑(elementaryLocusSamples shape r m n) ⊆ elementaryLocus shape r ∧
      (elementaryLocusSamples shape r m n).card =
        (match shape with
          | .point => 1
          | .line _ => m + n + 1
          | .fibre => (m + 1) * (n + 1)) ∧
      ((∀ w ∈ elementaryLocus shape r,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ↔
       (∀ w ∈ elementaryLocusSamples shape r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0)) := by
  intro shape r
  refine ⟨samples_subset shape r m n, samples_card shape r m n, ?_⟩
  constructor
  · intro h w hw
    exact h w (samples_subset shape r m n hw)
  · intro h
    change ∀ w ∈ elementaryLocus shape r, locusValue S Q w = 0
    change ∀ w ∈ elementaryLocusSamples shape r m n, locusValue S Q w = 0 at h
    cases shape with
    | point =>
      rintro w ⟨v, hv, rfl⟩
      have hv0 : v = 0 := hv
      simpa [hv0] using h r (by simp [elementaryLocusSamples])
    | line α => exact line_from_samples S Q m n hQ r α h
    | fibre => exact fibre_from_samples S Q m n hQ r h

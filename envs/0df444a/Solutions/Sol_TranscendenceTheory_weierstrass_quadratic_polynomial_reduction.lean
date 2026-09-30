-- Prove2me | solution 1 for TranscendenceTheory.weierstrass_quadratic_polynomial_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T20:00:55.638972+00:00
-- url     : https://prove2.me/submissions/780ac975-3b08-4f38-9974-16de5990a15b

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

noncomputable section
open MvPolynomial
open scoped Classical

private lemma degree_zero_add
    {R σ : Type*} [CommRing R] (i : σ) (a b : MvPolynomial σ R)
    (ha : a.degreeOf i = 0) (hb : b.degreeOf i = 0) :
    (a + b).degreeOf i = 0 := by
  exact Nat.eq_zero_of_le_zero ((degreeOf_add_le i a b).trans (by simp [ha, hb]))

private lemma degree_zero_mul
    {R σ : Type*} [CommRing R] (i : σ) (a b : MvPolynomial σ R)
    (ha : a.degreeOf i = 0) (hb : b.degreeOf i = 0) :
    (a * b).degreeOf i = 0 := by
  exact Nat.eq_zero_of_le_zero ((degreeOf_mul_le i a b).trans (by simp [ha, hb]))

private lemma quadratic_decomposition
    {R σ : Type*} [CommRing R] (i : σ) (h : MvPolynomial σ R)
    (hh : h.degreeOf i = 0) (p : MvPolynomial σ R) :
    ∃ a b c : MvPolynomial σ R, a.degreeOf i = 0 ∧ b.degreeOf i = 0 ∧
      p = a + X i * b + (X i ^ 2 - h) * c := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨C r, 0, 0, by simp, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, c, ha, hb, hp⟩ := hp
    obtain ⟨d, e, f, hd, he, hq⟩ := hq
    refine ⟨a + d, b + e, c + f, degree_zero_add i a d ha hd,
      degree_zero_add i b e hb he, ?_⟩
    rw [hp, hq]
    ring
  | mul_X p j hp =>
    obtain ⟨a, b, c, ha, hb, hp⟩ := hp
    by_cases hji : j = i
    · subst j
      refine ⟨h * b, a, b + X i * c, degree_zero_mul i h b hh hb, ha, ?_⟩
      rw [hp]
      ring
    · refine ⟨a * X j, b * X j, c * X j, ?_, ?_, ?_⟩
      · rw [degreeOf_mul_X_of_ne _ (Ne.symm hji), ha]
      · rw [degreeOf_mul_X_of_ne _ (Ne.symm hji), hb]
      · rw [hp]; ring

private lemma quadratic_reduction_map
    {R σ : Type*} [CommRing R] (i : σ) (h : MvPolynomial σ R)
    (hh : h.degreeOf i = 0) :
    ∃ ρ : MvPolynomial σ R → MvPolynomial σ R, ∀ p,
      (ρ p).degreeOf i ≤ 1 ∧
      p - ρ p ∈ Ideal.span ({X i ^ 2 - h} : Set (MvPolynomial σ R)) := by
  classical
  choose a b c ha hb hp using quadratic_decomposition i h hh
  refine ⟨fun p => a p + X i * b p, ?_⟩
  intro p
  constructor
  · apply (degreeOf_add_le i _ _).trans
    apply max_le
    · simp [ha p]
    · rw [mul_comm (X i) (b p)]
      exact (degreeOf_mul_X_self i (b p)).trans (by simp [hb p])
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨c p, ?_⟩
    exact sub_eq_iff_eq_add.mpr ((hp p).trans (add_comm _ _))

theorem solution
    (R : Type*) [CommRing R] (g₂ g₃ : R) :
    let q : MvPolynomial (Fin 4) R :=
      X 2 ^ 2 - C 4 * X 1 ^ 3 + C g₂ * X 1 + C g₃
    ∃ ρ : MvPolynomial (Fin 4) R → MvPolynomial (Fin 4) R, ∀ p,
      (ρ p).degreeOf (2 : Fin 4) ≤ 1 ∧
      p - ρ p ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 4) R)) := by
  let h : MvPolynomial (Fin 4) R := C 4 * X 1 ^ 3 + C (-g₂) * X 1 + C (-g₃)
  have hh : h.degreeOf (2 : Fin 4) = 0 :=
    degree_zero_add 2 _ _
      (degree_zero_add 2 _ _
        (degree_zero_mul 2 _ _ (degreeOf_C 4 2)
          (degreeOf_X_pow_of_ne 3 (by decide)))
        (degree_zero_mul 2 _ _ (degreeOf_C (-g₂) 2)
          (degreeOf_X_of_ne (by decide))))
      (degreeOf_C (-g₃) 2)
  have hrel : X (2 : Fin 4) ^ 2 - h =
      X 2 ^ 2 - C 4 * X 1 ^ 3 + C g₂ * X 1 + C g₃ := by
    simp only [h, map_neg]
    ring
  obtain ⟨ρ, hρ⟩ := quadratic_reduction_map (2 : Fin 4) h hh
  refine ⟨ρ, ?_⟩
  intro p
  simpa only [hrel] using hρ p

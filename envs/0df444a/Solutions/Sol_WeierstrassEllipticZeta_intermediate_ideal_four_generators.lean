-- Prove2me | solution 1 for WeierstrassEllipticZeta.intermediate_ideal_four_generators
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T17:45:11.743222+00:00
-- url     : https://prove2.me/submissions/c585f3fc-2022-4f1d-84da-b3f3962fe354

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Span

noncomputable section


private lemma four_generators_time_degree (p : Polynomial ℂ) :
    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) p).totalDegree ≤ p.natDegree := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  rw [MvPolynomial.totalDegree_X_pow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)

theorem solution
    (I J : Ideal (MvPolynomial (Fin 4) ℂ)) (M g : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (d : ℕ)
    (hI : I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
      (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
        Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i)))))
    (hJ : J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g})
    (hdiv : g ∣ M) (hg : g.natDegree ≤ d)
    (hr : ∀ i : Fin 3, (r i).natDegree ≤ d)
    (D : Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ))
    (hD : ∀ (p : MvPolynomial (Fin 4) ℂ) (k : ℕ),
      (D^[k] p).totalDegree ≤ p.totalDegree + k) :
    let f : Fin 4 → MvPolynomial (Fin 4) ℂ :=
      Fin.cons (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g)
        (fun i : Fin 3 => MvPolynomial.X i.succ -
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i))
    J = Ideal.span (Set.range f) ∧
      (∀ i : Fin 4, (f i).totalDegree ≤ max 1 d) ∧
      (∀ (k : ℕ) (i : Fin (k + 1) × Fin 4),
        (D^[i.1.val] (f i.2)).totalDegree ≤ max 1 d + k) := by
  classical
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  let R : Fin 3 → MvPolynomial (Fin 4) ℂ := fun i => MvPolynomial.X i.succ - E (r i)
  let f : Fin 4 → MvPolynomial (Fin 4) ℂ := Fin.cons (E g) R
  have hsmall : Ideal.span {E M} ≤ Ideal.span {E g} := by
    apply Ideal.span_le.mpr
    rintro p (rfl : p = E M)
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (E g))
  have hgen : J = Ideal.span (Set.range f) := by
    rw [hJ, hI]
    change Ideal.span (insert (E M) (Set.range R)) ⊔ Ideal.span {E g} =
      Ideal.span (Set.range (Fin.cons (E g) R))
    rw [Fin.range_cons, Ideal.span_insert, Ideal.span_insert]
    calc
      (Ideal.span {E M} ⊔ Ideal.span (Set.range R)) ⊔ Ideal.span {E g} =
          (Ideal.span {E M} ⊔ Ideal.span {E g}) ⊔ Ideal.span (Set.range R) := by ac_rfl
      _ = Ideal.span {E g} ⊔ Ideal.span (Set.range R) := by rw [sup_eq_right.mpr hsmall]
  have hdegree : ∀ i : Fin 4, (f i).totalDegree ≤ max 1 d := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((four_generators_time_degree g).trans hg).trans (le_max_right _ _)
    · change (MvPolynomial.X j.succ - E (r j)).totalDegree ≤ max 1 d
      rw [sub_eq_add_neg]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · simp [MvPolynomial.totalDegree_X]
      · simpa only [neg_one_smul] using
          ((MvPolynomial.totalDegree_smul_le (-1 : ℂ) (E (r j))).trans
            ((four_generators_time_degree (r j)).trans (hr j))).trans (le_max_right 1 _)
  refine ⟨hgen, hdegree, ?_⟩
  intro k i
  change (D^[i.1.val] (f i.2)).totalDegree ≤ max 1 d + k
  apply (hD _ _).trans
  have hf := hdegree i.2
  have hi := i.1.isLt
  omega


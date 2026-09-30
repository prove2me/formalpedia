-- Prove2me | solution 1 for WeierstrassEllipticZeta.time_normal_form_triangular_generators
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T22:42:22.254368+00:00
-- url     : https://prove2.me/submissions/9fbfb1ad-5dc4-4832-9dd7-495207b6a7ff

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section


theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (d : ℕ) (M : Polynomial ℂ)
    (hM : M.Monic) (hdegree : M.degree = (d : ℕ))
    (hMI : Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M ∈ I)
    (hrep : ∀ p : MvPolynomial (Fin 4) ℂ, ∃! q : Polynomial ℂ,
      q.degree < (d : ℕ) ∧ p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ I) :
    ∃ r : Fin 3 → Polynomial ℂ,
      (∀ i, (r i).degree < (d : ℕ)) ∧
      I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
        (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i)))) ∧
      ∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p := by
  classical
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  choose r hr hunique using fun i : Fin 3 => hrep (MvPolynomial.X i.succ)
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
    Ideal.span (insert (E M) (Set.range fun i : Fin 3 => MvPolynomial.X i.succ - E (r i)))
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro p (rfl | ⟨i, rfl⟩)
    · exact hMI
    · exact (hr i).2
  have hMJ : E M ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hrJ (i : Fin 3) : MvPolynomial.X i.succ - E (r i) ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i))
  let π := Ideal.Quotient.mkₐ ℂ J
  have heval : π = (π.comp E).comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [φ, E]
    · simpa [φ, E, π] using
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J) _ _).mpr (hrJ j)
  have hsub (p : MvPolynomial (Fin 4) ℂ) : p - E (φ p) ∈ J := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J) _ _).mp
    exact AlgHom.congr_fun heval p
  have hsmall (q : Polynomial ℂ) (hq : q.degree < (d : ℕ)) (hIq : E q ∈ I) : q = 0 := by
    obtain ⟨s, hs, hu⟩ := hrep 0
    have hzero : (0 : Polynomial ℂ) = s := hu 0 ⟨by simp, by simp⟩
    have hqeq : q = s := hu q ⟨hq, by simpa [E] using I.neg_mem hIq⟩
    exact hqeq.trans hzero.symm
  have htime (q : Polynomial ℂ) : E q ∈ I ↔ M ∣ q := by
    constructor
    · intro hq
      have hmul : E M * E (q /ₘ M) ∈ I := I.mul_mem_right _ hMI
      have hdiv := congrArg E (Polynomial.modByMonic_add_div q M)
      simp only [map_add, map_mul] at hdiv
      have hrem : E (q %ₘ M) ∈ I := by
        apply (I.add_mem_iff_left hmul).mp
        rwa [hdiv]
      exact (Polynomial.modByMonic_eq_zero_iff_dvd hM).mp
        (hsmall _ (hdegree ▸ Polynomial.degree_modByMonic_lt q hM) hrem)
    · rintro ⟨q', rfl⟩
      rw [map_mul]
      exact I.mul_mem_right _ hMI
  have hcriterion (p : MvPolynomial (Fin 4) ℂ) : p ∈ I ↔ M ∣ φ p := by
    rw [← htime]
    constructor
    · intro hp
      have h := I.sub_mem hp (hJI (hsub p))
      simpa only [sub_sub_cancel] using h
    · intro hp
      have h := I.add_mem (hJI (hsub p)) hp
      simpa only [sub_add_cancel] using h
  refine ⟨r, fun i => (hr i).1, le_antisymm ?_ hJI, hcriterion⟩
  intro p hp
  obtain ⟨q, hq⟩ := (hcriterion p).mp hp
  have hEp : E (φ p) ∈ J := by
    rw [hq, map_mul]
    exact J.mul_mem_right _ hMJ
  have h := J.add_mem (hsub p) hEp
  simpa only [sub_add_cancel] using h


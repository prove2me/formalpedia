-- Prove2me | solution 1 for WeierstrassEllipticZeta.evaluation_kernel_adjoin_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T15:57:55.153344+00:00
-- url     : https://prove2.me/submissions/54d43575-294e-4600-a684-f3af2bdb1686

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Polynomial.Basic



theorem solution
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (x : A) (m : Polynomial R)
    (hker : ∀ q : Polynomial R, q.eval₂ (algebraMap R A) x = 0 ↔ m ∣ q) :
    ∃! e : (Polynomial R ⧸ Ideal.span ({m} : Set (Polynomial R))) ≃ₐ[R]
        Algebra.adjoin R ({x} : Set A),
      ∀ q : Polynomial R,
        (e (Ideal.Quotient.mk (Ideal.span {m}) q) : A) =
          q.eval₂ (algebraMap R A) x := by
  let E : Polynomial R →ₐ[R] A := Polynomial.aeval x
  have hI : Ideal.span ({m} : Set (Polynomial R)) = RingHom.ker E := by
    ext q
    simpa only [Ideal.mem_span_singleton, RingHom.mem_ker, E, Polynomial.aeval_def] using
      (hker q).symm
  let e := (Ideal.quotientEquivAlgOfEq R hI).trans
    ((Ideal.quotientKerEquivRange E).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval R x).symm))
  have he : ∀ q : Polynomial R,
      (e (Ideal.Quotient.mk (Ideal.span {m}) q) : A) =
        q.eval₂ (algebraMap R A) x := by
    intro q
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply AlgEquiv.ext
  intro a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Subtype.ext
  exact (he' q).trans (he q).symm


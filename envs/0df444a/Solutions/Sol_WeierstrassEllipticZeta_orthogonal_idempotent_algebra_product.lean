-- Prove2me | solution 1 for WeierstrassEllipticZeta.orthogonal_idempotent_algebra_product
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T18:31:30.227617+00:00
-- url     : https://prove2.me/submissions/6af96934-df61-40c9-ad31-4c36c2ed628b

import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Algebra.Pi

open scoped Classical



theorem solution
    (R B ι : Type*) [CommRing R] [CommRing B] [Algebra R B] [Fintype ι]
    (ε : ι → B) (hidem : ∀ i, IsIdempotentElem (ε i))
    (horth : ∀ i j, i ≠ j → ε i * ε j = 0) (hsum : (∑ i, ε i) = 1) :
    (∀ i a, a ∈ Ideal.span ({1 - ε i} : Set B) ↔ ε i * a = 0) ∧
    ∃ Φ : B ≃ₐ[R] (∀ i, B ⧸ Ideal.span ({1 - ε i} : Set B)),
      (∀ a i, Φ a i = Ideal.Quotient.mk (Ideal.span {1 - ε i}) a) ∧
      ∀ i j, Φ (ε j) i = if i = j then 1 else 0 := by
  classical
  have hker (i : ι) (a : B) :
      a ∈ Ideal.span ({1 - ε i} : Set B) ↔ ε i * a = 0 := by
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, rfl⟩
      rw [← mul_assoc, (hidem i).mul_one_sub_self, zero_mul]
    · intro h
      exact ⟨a, by rw [sub_mul, one_mul, h, sub_zero]⟩
  have hε : CompleteOrthogonalIdempotents ε :=
    { idem := hidem
      ortho := fun i j hij => horth i j hij
      complete := hsum }
  let φ : B →ₐ[R] (∀ i, B ⧸ Ideal.span ({1 - ε i} : Set B)) :=
    AlgHom.pi fun i => Ideal.Quotient.mkₐ R (Ideal.span {1 - ε i})
  let Φ := AlgEquiv.ofBijective φ hε.bijective_pi
  refine ⟨hker, Φ, fun _ _ => rfl, ?_⟩
  intro i j
  change Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε j) = _
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Ideal.Quotient.mk_eq_one_iff_sub_mem, hker]
    rw [mul_sub, (hidem i).eq, mul_one, sub_self]
  · rw [if_neg hij, Ideal.Quotient.eq_zero_iff_mem, hker]
    exact horth i j hij


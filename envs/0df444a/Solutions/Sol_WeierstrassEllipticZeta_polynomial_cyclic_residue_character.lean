-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_residue_character
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T03:49:06.536177+00:00
-- url     : https://prove2.me/submissions/07cf3fa1-e707-4367-8e67-919bbc05360c

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Defs



open Polynomial

theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (x : A) (z : K)
    (hsurj : Function.Surjective (fun q : Polynomial K =>
      q.eval₂ (algebraMap K A) x))
    (hnil : ∀ q : Polynomial K,
      IsNilpotent (q.eval₂ (algebraMap K A) x) ↔ q.eval z = 0) :
    ∃! χ : A →ₐ[K] K,
      (∀ q : Polynomial K, χ (q.eval₂ (algebraMap K A) x) = q.eval z) ∧
      (∀ a : A, χ a = 0 ↔ IsNilpotent a) ∧ Function.Surjective χ := by
  let f : Polynomial K →ₐ[K] A := aeval x
  let g : Polynomial K →ₐ[K] K := aeval z
  have hf : Function.Surjective f := hsurj
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom := by
    intro q hq
    change q.eval₂ (algebraMap K A) x = 0 at hq
    have hn : IsNilpotent (q.eval₂ (algebraMap K A) x) := by
      rw [hq]
      exact ⟨1, pow_one 0⟩
    exact (hnil q).mp hn
  let χ : A →ₐ[K] K := AlgHom.liftOfSurjective f hf g hker
  have hχ : ∀ q : Polynomial K, χ (q.eval₂ (algebraMap K A) x) = q.eval z := by
    intro q
    exact AlgHom.liftOfSurjective_apply f hf g hker q
  refine ⟨χ, ⟨hχ, ?_, ?_⟩, ?_⟩
  · intro a
    obtain ⟨q, rfl⟩ := hsurj a
    rw [hχ]
    exact (hnil q).symm
  · intro k
    exact ⟨algebraMap K A k, χ.commutes k⟩
  · intro ψ hψ
    ext a
    obtain ⟨q, rfl⟩ := hsurj a
    exact (hψ.1 q).trans (hχ q).symm


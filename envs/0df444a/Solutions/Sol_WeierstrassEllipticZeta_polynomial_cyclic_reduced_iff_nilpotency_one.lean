-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_reduced_iff_nilpotency_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T03:03:13.674114+00:00
-- url     : https://prove2.me/submissions/995c50b3-8643-44b2-81cf-2ad6d9f83bc1

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.RingTheory.Nilpotent.Defs



open Polynomial

theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    (x : A) (z : K)
    (hsurj : Function.Surjective (fun q : Polynomial K => q.eval₂ (algebraMap K A) x))
    (hnil : IsNilpotent (x - algebraMap K A z)) :
    (IsReduced A ↔ x = algebraMap K A z) ∧
      (IsReduced A ↔ nilpotencyClass (x - algebraMap K A z) = 1) := by
  have hscalar : IsReduced A ↔ x = algebraMap K A z := by
    constructor
    · intro h
      let := h
      exact sub_eq_zero.mp hnil.eq_zero
    · intro hx
      refine ⟨fun a ha => ?_⟩
      obtain ⟨q, rfl⟩ := hsurj a
      simp only [hx, eval₂_at_apply] at ha ⊢
      have hq : IsNilpotent (q.eval z) :=
        (IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective K A)).mp ha
      rw [hq.eq_zero, map_zero]
  refine ⟨hscalar, ?_⟩
  simpa only [nilpotencyClass_eq_one, sub_eq_zero] using hscalar


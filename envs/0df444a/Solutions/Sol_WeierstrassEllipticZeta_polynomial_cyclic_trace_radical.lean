-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_trace_radical
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T02:09:10.145114+00:00
-- url     : https://prove2.me/submissions/9731b32f-6224-48f7-af22-7da9aa7d9c68

import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.Polynomial.Eval.Algebra



open Polynomial

theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
    (x : A) (z c : K) (hc : c ≠ 0)
    (hsurj : Function.Surjective (fun q : Polynomial K => q.eval₂ (algebraMap K A) x))
    (htrace : ∀ q : Polynomial K,
      LinearMap.trace K A (Algebra.lmul K A (q.eval₂ (algebraMap K A) x)) = c * q.eval z)
    (hnil : ∀ q : Polynomial K, IsNilpotent (q.eval₂ (algebraMap K A) x) ↔ q.eval z = 0) :
    (∀ a : A, (∀ b : A, Algebra.traceForm K A a b = 0) ↔ IsNilpotent a) ∧
      ((Algebra.traceForm K A).Nondegenerate ↔ IsReduced A) := by
  have hpair (q r : Polynomial K) :
      Algebra.traceForm K A (q.eval₂ (algebraMap K A) x) (r.eval₂ (algebraMap K A) x) =
        c * q.eval z * r.eval z := by
    rw [Algebra.traceForm_apply, ← eval₂_mul, Algebra.trace_apply, htrace, eval_mul,
      mul_assoc]
  have hrad (a : A) : (∀ b : A, Algebra.traceForm K A a b = 0) ↔ IsNilpotent a := by
    obtain ⟨q, rfl⟩ := hsurj a
    rw [hnil]
    constructor
    · intro h
      have hzero := h 1
      rw [Algebra.traceForm_apply, mul_one, Algebra.trace_apply, htrace] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hc
    · intro h b
      obtain ⟨r, rfl⟩ := hsurj b
      rw [hpair, h, mul_zero, zero_mul]
  refine ⟨hrad, ?_⟩
  rw [LinearMap.BilinForm.Nondegenerate,
    (Algebra.traceForm_isSymm K (S := A)).isRefl.nondegenerate_iff_separatingLeft]
  simp only [LinearMap.SeparatingLeft, hrad, isReduced_iff]


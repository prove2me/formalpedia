-- Prove2me | solution 1 for WeierstrassEllipticZeta.monic_time_polynomial_derivative_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T18:54:18.441404+00:00
-- url     : https://prove2.me/submissions/29561e83-2f7d-423d-852b-30f373a24235

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Span

noncomputable section



theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (t : A) (ht : D t = 1)
    (g : Polynomial ℂ) (hg : g.Monic) :
    (∀ k : ℕ, D^[k] (Polynomial.aeval t g) =
      Polynomial.aeval t (Polynomial.derivative^[k] g)) ∧
    D^[g.natDegree] (Polynomial.aeval t g) =
      algebraMap ℂ A (g.natDegree.factorial : ℂ) ∧
    (g.natDegree.factorial : ℂ)⁻¹ • D^[g.natDegree] (Polynomial.aeval t g) = 1 ∧
    (∀ k : ℕ, g.natDegree < k → D^[k] (Polynomial.aeval t g) = 0) ∧
    (∀ k : ℕ, g.natDegree ≤ k →
      Ideal.span (Set.range (fun i : Fin (k + 1) =>
        D^[i.val] (Polynomial.aeval t g))) = ⊤) := by
  have hiterate (k : ℕ) : D^[k] (Polynomial.aeval t g) =
      Polynomial.aeval t (Polynomial.derivative^[k] g) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.map_aeval, ht,
        smul_eq_mul, mul_one, Function.iterate_succ_apply']
  have hconstant : Polynomial.derivative^[g.natDegree] g =
      Polynomial.C (g.natDegree.factorial : ℂ) := by
    have hdegree : (Polynomial.derivative^[g.natDegree] g).natDegree ≤ 0 := by
      simpa using Polynomial.natDegree_iterate_derivative g g.natDegree
    rw [Polynomial.eq_C_of_natDegree_le_zero hdegree, Polynomial.coeff_iterate_derivative]
    simp [Nat.descFactorial_self, hg.coeff_natDegree]
  have hvalue : D^[g.natDegree] (Polynomial.aeval t g) =
      algebraMap ℂ A (g.natDegree.factorial : ℂ) := by
    rw [hiterate, hconstant, Polynomial.aeval_C]
  have hfactorial : (g.natDegree.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero g.natDegree
  have hunit : (g.natDegree.factorial : ℂ)⁻¹ •
      D^[g.natDegree] (Polynomial.aeval t g) = 1 := by
    rw [hvalue, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hfactorial, map_one]
  refine ⟨hiterate, hvalue, hunit, ?_, ?_⟩
  · intro k hk
    rw [hiterate, Polynomial.iterate_derivative_eq_zero hk, map_zero]
  · intro k hk
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hunit]
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    exact ⟨⟨g.natDegree, Nat.lt_succ_of_le hk⟩, rfl⟩


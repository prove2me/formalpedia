-- Prove2me | solution 1 for ShiShallow.eigenvalues_nonneg_of_quadratic_form_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T01:26:24.674768+00:00
-- url     : https://prove2.me/submissions/5c8571eb-bc75-4531-af9e-b6ab7dddfb01

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-!
# Eigenvalues of a Hermitian matrix with nonnegative quadratic form are nonnegative

Strategy (mirror of `eigenvalues_le_of_quadratic_form_le`, inequality flipped): the sum form
of the quadratic form is definitionally the `dotProduct` form; `eigenvalues_eq` says the
`i`-th eigenvalue *is* the real part of that form at the `i`-th eigenvector basis member;
so the hypothesis instantiated at that vector is literally the goal. No unit-norm step is
needed here because the bound carries no norm factor.

API used (Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474):
* `Matrix.IsHermitian.eigenvalues`       Mathlib/Analysis/Matrix/Spectrum.lean:65
* `Matrix.IsHermitian.eigenvectorBasis`  Mathlib/Analysis/Matrix/Spectrum.lean:69
* `Matrix.IsHermitian.eigenvalues_eq`    Mathlib/Analysis/Matrix/Spectrum.lean:146
* `dotProduct` (root-level)              Mathlib/Data/Matrix/Mul.lean:72
* `starRingEnd_apply`                    Mathlib/Algebra/Star/Basic.lean:351
* `RCLike.re_to_complex`                 Mathlib/Analysis/Complex/Basic.lean:491
-/

/-- The explicit sum form of the quadratic form is (definitionally) the `dotProduct` form used
by `Matrix.IsHermitian.eigenvalues_eq`. -/
private lemma shiPsd2_quadForm_eq_dotProduct {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (u : Bits w → ℂ) :
    (∑ y : Bits w, (starRingEnd ℂ) (u y) * Matrix.mulVec M u y)
      = dotProduct (star u) (Matrix.mulVec M u) := by
  first
  | (rfl
     done)
  | (simp only [dotProduct, Pi.star_apply, starRingEnd_apply]
     done)
  | (unfold dotProduct
     refine Finset.sum_congr rfl fun y _ => ?_
     simp only [Pi.star_apply, starRingEnd_apply]
     done)

/-- A vector (a member of the eigenvector basis) whose Rayleigh numerator is exactly the
`i`-th eigenvalue. Stated existentially so no `WithLp`/`PiLp` coercion appears downstream. -/
private lemma shiPsd2_exists_eigenvector {w : ℕ}
    {M : Matrix (Bits w) (Bits w) ℂ} (hM : M.IsHermitian) (i : Bits w) :
    ∃ u : Bits w → ℂ,
      hM.eigenvalues i = (dotProduct (star u) (Matrix.mulVec M u)).re := by
  refine ⟨WithLp.ofLp (hM.eigenvectorBasis i), ?_⟩
  have h := hM.eigenvalues_eq i
  first
  | (exact h
     done)
  | (simpa using h
     done)
  | (simp only [RCLike.re_to_complex] at h
     exact h
     done)

theorem solution {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian)
    (hb : ∀ v : Bits w → ℂ,
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec M v y).re)
    (i : Bits w) :
    0 ≤ hM.eigenvalues i := by
  obtain ⟨u, heig⟩ := shiPsd2_exists_eigenvector hM i
  have key := hb u
  rw [shiPsd2_quadForm_eq_dotProduct] at key
  rw [heig]
  exact key

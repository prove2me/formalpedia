-- Prove2me | solution 1 for ShiShallow.eigenvalues_le_of_quadratic_form_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T23:14:18.172538+00:00
-- url     : https://prove2.me/submissions/4294750e-b1c4-4278-a4e5-7559e4c04cc6

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-!
# Eigenvalue bound from a quadratic-form bound (Hermitian matrix)

The quadratic form is written with `Matrix.mulVec` only (no scoped matrix notations) and is
evaluated at the `i`-th member of `Matrix.IsHermitian.eigenvectorBasis`.

API used (Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474):
* `Matrix.IsHermitian.eigenvalues`        Mathlib/Analysis/Matrix/Spectrum.lean:65
* `Matrix.IsHermitian.eigenvectorBasis`   Mathlib/Analysis/Matrix/Spectrum.lean:69
* `Matrix.IsHermitian.eigenvalues_eq`     Mathlib/Analysis/Matrix/Spectrum.lean:146
* `OrthonormalBasis.norm_eq_one`          Mathlib/Analysis/InnerProductSpace/PiL2.lean:457
* `EuclideanSpace.norm_sq_eq`             Mathlib/Analysis/InnerProductSpace/PiL2.lean:151
* `dotProduct` (root-level, unqualified)  Mathlib/Data/Matrix/Mul.lean:72
* `starRingEnd_apply`                     Mathlib/Algebra/Star/Basic.lean:351
* `RCLike.re_to_complex`                  Mathlib/Analysis/Complex/Basic.lean:491
-/

/-- The explicit sum form of the quadratic form is *definitionally* the `dotProduct` form used
by `Matrix.IsHermitian.eigenvalues_eq`: `dotProduct v w` unfolds to `∑ i, v i * w i`,
`(star u) y` unfolds to `star (u y)` through `Pi.instStar`, and `starRingEnd ℂ` applies as
`star` by `starRingEnd_apply`, which is proved by `rfl`. -/
private lemma shiFin3_quadForm_eq_dotProduct {w : ℕ}
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

/-- There is a unit vector `u` (a member of the eigenvector basis) whose Rayleigh quotient is
exactly the `i`-th eigenvalue. Stated existentially so that no `WithLp`/`PiLp` coercion has to
appear in a consumed statement. -/
private lemma shiFin3_exists_unit_eigenvector {w : ℕ}
    {M : Matrix (Bits w) (Bits w) ℂ} (hM : M.IsHermitian) (i : Bits w) :
    ∃ u : Bits w → ℂ, (∑ y : Bits w, ‖u y‖ ^ 2) = 1 ∧
      hM.eigenvalues i = (dotProduct (star u) (Matrix.mulVec M u)).re := by
  refine ⟨WithLp.ofLp (hM.eigenvectorBasis i), ?_, ?_⟩
  · have hone : ‖hM.eigenvectorBasis i‖ = 1 :=
      hM.eigenvectorBasis.norm_eq_one i
    have hsq := EuclideanSpace.norm_sq_eq (hM.eigenvectorBasis i)
    rw [hone, one_pow] at hsq
    first
      | (exact hsq.symm
         done)
      | (simpa using hsq.symm
         done)
  · have h := hM.eigenvalues_eq i
    first
      | (exact h
         done)
      | (simpa using h
         done)
      | (simp only [RCLike.re_to_complex] at h
         exact h
         done)

theorem solution {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian) (s : ℝ)
    (hb : ∀ v : Bits w → ℂ,
      (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec M v y).re
        ≤ s * ∑ y : Bits w, ‖v y‖ ^ 2)
    (i : Bits w) :
    hM.eigenvalues i ≤ s := by
  obtain ⟨u, hunit, heig⟩ := shiFin3_exists_unit_eigenvector hM i
  have key := hb u
  rw [shiFin3_quadForm_eq_dotProduct, hunit, mul_one] at key
  rw [heig]
  exact key

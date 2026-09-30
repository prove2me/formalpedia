-- Prove2me | solution 1 for WeierstrassEllipticZeta.weighted_generalized_eigenspace_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T15:43:24.474248+00:00
-- url     : https://prove2.me/submissions/8d9fb000-85bb-4186-a4a3-7c0c1c36bece

import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Polynomial.Roots

open scoped Classical



theorem solution
    (K : Type*) [Field K] (n : ℕ) (V : Type*) [Fintype V]
    (A : Matrix (Fin n) (Fin n) K) (w : V → ℕ) (f : V → K)
    (hchar : A.charpoly = ∏ v : V, (Polynomial.X - Polynomial.C (f v)) ^ w v) :
    ∀ z : K,
      Module.finrank K (Module.End.maxGenEigenspace A.mulVecLin z) =
        ∑ v ∈ Finset.univ.filter (fun v : V => f v = z), w v ∧
      ∀ N : ℕ, n ≤ N →
        Module.finrank K (Module.End.genEigenspace A.mulVecLin z N) =
          ∑ v ∈ Finset.univ.filter (fun v : V => f v = z), w v := by
  classical
  intro z
  have hne (v : V) : (Polynomial.X - Polynomial.C (f v)) ^ w v ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hfactor (v : V) :
      ((Polynomial.X - Polynomial.C (f v)) ^ w v).rootMultiplicity z =
        if f v = z then w v else 0 := by
    by_cases h : f v = z
    · rw [if_pos h, h, Polynomial.rootMultiplicity_X_sub_C_pow]
    · rw [if_neg h]
      apply Polynomial.rootMultiplicity_eq_zero
      simp only [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h))
  have hprod (s : Finset V) :
      (∏ v ∈ s, (Polynomial.X - Polynomial.C (f v)) ^ w v).rootMultiplicity z =
        ∑ v ∈ s, (if f v = z then w v else 0) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
      rw [Finset.prod_insert hv, Finset.sum_insert hv,
        Polynomial.rootMultiplicity_mul (mul_ne_zero (hne v)
          (Finset.prod_ne_zero_iff.mpr (fun u _ => hne u))), hfactor v, ih]
  have hmax : Module.finrank K (Module.End.maxGenEigenspace A.mulVecLin z) =
      ∑ v ∈ Finset.univ.filter (fun v : V => f v = z), w v := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_mulVecLin,
      hchar, hprod, Finset.sum_filter]
  refine ⟨hmax, ?_⟩
  intro N hN
  have hdim : Module.finrank K (Fin n → K) = n := by simp
  have hg := Module.End.genEigenspace_eq_genEigenspace_finrank_of_le A.mulVecLin z
    (show Module.finrank K (Fin n → K) ≤ N by simpa only [hdim] using hN)
  rw [← Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at hg
  rw [hg]
  exact hmax


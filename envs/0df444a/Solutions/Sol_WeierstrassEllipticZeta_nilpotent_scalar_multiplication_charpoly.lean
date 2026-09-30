-- Prove2me | solution 1 for WeierstrassEllipticZeta.nilpotent_scalar_multiplication_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T00:26:15.811005+00:00
-- url     : https://prove2.me/submissions/d07c5b67-29bf-4a6d-a4d4-01d8ca7ef16e

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Zero



open Polynomial

theorem solution
    (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (a : A) (z : K) (h : IsNilpotent (a - algebraMap K A z)) :
    (Algebra.lmul K A a).charpoly = (X - C z) ^ Module.finrank K A := by
  have hp := (h.map (Algebra.lmul K A)).charpoly_eq_X_pow_finrank
  have hshift : Algebra.lmul K A (a - algebraMap K A z) =
      Algebra.lmul K A a - z • 1 := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rw [hshift, LinearMap.charpoly_sub_smul] at hp
  have hc := congrArg (fun p : Polynomial K => p.comp (X - C z)) hp
  simpa only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X, Polynomial.pow_comp] using hc


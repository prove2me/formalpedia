-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_scalar_shift_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T20:46:41.104704+00:00
-- url     : https://prove2.me/submissions/a3b5fa0a-4953-4ed7-9f76-2d25b48a84cd

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations



theorem solution
    (K B V : Type*) [CommRing K] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] (e : B →ₗ[K] V)
    (he : Function.Injective e) (P : Module.End K V)
    (α ε : B) (J : Ideal B) (z : K) (n : ℕ)
    (hJ : ∀ a, a ∈ J ↔ ε * a = 0)
    (hP : ∀ a, P (e a) = e (α * a))
    (hε : e ε ∈ Module.End.genEigenspace P z n) :
    (Ideal.Quotient.mk J α - algebraMap K (B ⧸ J) z) ^ n = 0 := by
  have hstep (a : B) :
      (P - z • 1) (e a) = e ((α - algebraMap K B z) * a) := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hP a, sub_mul, map_sub, ← Algebra.smul_def, map_smul]
  have hp (k : ℕ) (a : B) :
      ((P - z • 1) ^ k) (e a) = e ((α - algebraMap K B z) ^ k * a) := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hk, hstep, pow_succ', mul_assoc]
  have hzero : e ((α - algebraMap K B z) ^ n * ε) = 0 := by
    rw [← hp n ε]
    exact Module.End.mem_genEigenspace_nat.mp hε
  have hann : ε * (α - algebraMap K B z) ^ n = 0 := by
    rw [mul_comm]
    exact he (hzero.trans (map_zero e).symm)
  have hq : Ideal.Quotient.mk J ((α - algebraMap K B z) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ((hJ _).mpr hann)
  simpa only [map_pow, map_sub, Ideal.Quotient.mk_algebraMap] using hq


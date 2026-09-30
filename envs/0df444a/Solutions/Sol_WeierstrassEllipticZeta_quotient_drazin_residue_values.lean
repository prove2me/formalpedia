-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_drazin_residue_values
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T03:24:41.145325+00:00
-- url     : https://prove2.me/submissions/2a939260-82b6-4d64-a5f1-895532ebc4e7

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Field.Basic

open scoped Classical



theorem solution
    (A K : Type*) [CommRing A] [Field K] (I : Ideal A) (φ : A →+* K)
    (hI : I ≤ RingHom.ker φ) (p q : A) (d : ℕ)
    (h₁ : Ideal.Quotient.mk I p * Ideal.Quotient.mk I q * Ideal.Quotient.mk I q =
      Ideal.Quotient.mk I q)
    (h₂ : (Ideal.Quotient.mk I p) ^ (d + 1) * Ideal.Quotient.mk I q =
      (Ideal.Quotient.mk I p) ^ d) :
    φ q = (φ p)⁻¹ ∧ φ (p * q) = if φ p = 0 then 0 else 1 := by
  let ψ : A ⧸ I →+* K :=
    Ideal.Quotient.lift I φ (fun a ha => RingHom.mem_ker.mp (hI ha))
  have h₁' : φ p * φ q * φ q = φ q := by
    simpa only [map_mul, ψ, Ideal.Quotient.lift_mk] using congrArg ψ h₁
  have h₂' : (φ p) ^ (d + 1) * φ q = (φ p) ^ d := by
    simpa only [map_mul, map_pow, ψ, Ideal.Quotient.lift_mk] using congrArg ψ h₂
  have hinv : φ q = (φ p)⁻¹ := by
    by_cases hp : φ p = 0
    · simpa only [hp, zero_mul, inv_zero] using h₁'.symm
    · have hmul : φ p * φ q = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero d hp)
        rw [← mul_assoc, ← pow_succ, h₂', mul_one]
      apply mul_left_cancel₀ hp
      rw [mul_inv_cancel₀ hp]
      exact hmul
  refine ⟨hinv, ?_⟩
  rw [map_mul, hinv]
  split_ifs with hp
  · rw [hp, zero_mul]
  · exact mul_inv_cancel₀ hp


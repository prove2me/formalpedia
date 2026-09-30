-- Prove2me | solution 1 for WeierstrassEllipticZeta.drazin_multiplication_projector
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T02:09:52.338212+00:00
-- url     : https://prove2.me/submissions/7ed4de03-a417-4c26-a7f3-8491b2df4e9c

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Ring



theorem solution
    (B : Type*) [CommRing B] [Algebra ℂ B] (a b : B) (d : ℕ)
    (h₁ : a * b * b = b) (h₂ : a ^ (d + 1) * b = a ^ d) :
    let f := Algebra.lmul ℂ B a
    let P := Algebra.lmul ℂ B (a * b)
    IsIdempotentElem (a * b) ∧ IsIdempotentElem P ∧
      LinearMap.ker P = LinearMap.ker (f ^ d) ∧
      LinearMap.range P = LinearMap.range (f ^ d) ∧
      ∃ h : IsCompl (LinearMap.range (f ^ d)) (LinearMap.ker (f ^ d)),
        P = (LinearMap.range (f ^ d)).projection (LinearMap.ker (f ^ d)) h := by
  dsimp only
  have he : IsIdempotentElem (a * b) := by
    change (a * b) * (a * b) = a * b
    calc
      (a * b) * (a * b) = a * (a * b * b) := by ring
      _ = a * b := by rw [h₁]
  have hfix : a ^ d * (a * b) = a ^ d := by
    rw [← mul_assoc, ← pow_succ, h₂]
  have hfactor : a * b = a ^ d * b ^ d := by
    by_cases hd : d = 0
    · subst d
      simpa only [Nat.zero_add, pow_zero, pow_one, one_mul] using h₂
    · rw [← mul_pow, he.pow_eq hd]
  have hP := he.map (Algebra.lmul ℂ B)
  have hker : LinearMap.ker (Algebra.lmul ℂ B (a * b)) =
      LinearMap.ker ((Algebra.lmul ℂ B a) ^ d) := by
    rw [← map_pow]
    ext x
    change (a * b) * x = 0 ↔ a ^ d * x = 0
    constructor
    · intro hx
      calc
        a ^ d * x = (a ^ d * (a * b)) * x := by rw [hfix]
        _ = 0 := by rw [mul_assoc, hx, mul_zero]
    · intro hx
      rw [hfactor, mul_comm (a ^ d), mul_assoc, hx, mul_zero]
  have hrange : LinearMap.range (Algebra.lmul ℂ B (a * b)) =
      LinearMap.range ((Algebra.lmul ℂ B a) ^ d) := by
    rw [← map_pow]
    ext x
    change (∃ y, (a * b) * y = x) ↔ ∃ y, a ^ d * y = x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨b ^ d * y, by rw [hfactor, mul_assoc]⟩
    · rintro ⟨y, rfl⟩
      refine ⟨a ^ d * y, ?_⟩
      rw [← mul_assoc, mul_comm (a * b), hfix]
  refine ⟨he, hP, hker, hrange, ?_⟩
  have hc := LinearMap.IsIdempotentElem.isCompl hP
  rw [hker, hrange] at hc
  refine ⟨hc, ?_⟩
  simpa only [hker, hrange] using LinearMap.IsIdempotentElem.eq_projection hP


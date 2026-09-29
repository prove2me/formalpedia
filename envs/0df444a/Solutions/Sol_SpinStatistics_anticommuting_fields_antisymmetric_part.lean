-- Prove2me | solution 1 for SpinStatistics.anticommuting_fields_antisymmetric_part
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T10:54:02.35098+00:00
-- url     : https://prove2.me/submissions/10f9b961-4743-4020-880c-3b133cbd63b7

import Mathlib
import Definitions.Def_SpinStatistics_Defs

set_option autoImplicit false

open SpinStatistics in
/-- Relabelling `x ↔ y` in the double sum over distinct pairs. -/
theorem twoParticleOp_swap_2cd9f4cc {X A : Type*} [Fintype X] [DecidableEq X]
    [Ring A] [Algebra ℂ A] (ψ : X → X → ℂ) (φ : X → A) :
    twoParticleOp (fun x y => ψ y x) φ =
      ∑ x, ∑ y ∈ Finset.univ.filter (fun y => x ≠ y), ψ x y • (φ y * φ x) := by
  unfold twoParticleOp
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rcases eq_or_ne x y with rfl | h
  · simp
  · simp [h, Ne.symm h]

open SpinStatistics in
/-- Linearity of `twoParticleOp` in a combination of `ψ` and its transpose. -/
theorem twoParticleOp_lin_2cd9f4cc {X A : Type*} [Fintype X] [DecidableEq X]
    [Ring A] [Algebra ℂ A] (a b : ℂ) (ψ : X → X → ℂ) (φ : X → A) :
    twoParticleOp (fun x y => a * ψ x y + b * ψ y x) φ =
      a • twoParticleOp ψ φ + b • twoParticleOp (fun x y => ψ y x) φ := by
  unfold twoParticleOp
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [add_smul, mul_smul, mul_smul]

open SpinStatistics in
theorem solution {X A : Type*} [Fintype X] [DecidableEq X]
    [Ring A] [Algebra ℂ A] (ψ : X → X → ℂ) (φ : X → A)
    (hanti : ∀ x y, x ≠ y → φ x * φ y = -(φ y * φ x)) :
    twoParticleOp ψ φ = twoParticleOp (antisymmPart ψ) φ ∧
      twoParticleOp (symmPart ψ) φ = 0 := by
  have hswap : twoParticleOp (fun x y => ψ y x) φ = -twoParticleOp ψ φ := by
    rw [twoParticleOp_swap_2cd9f4cc]
    unfold twoParticleOp
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have hxy : x ≠ y := (Finset.mem_filter.mp hy).2
    rw [hanti y x (Ne.symm hxy), smul_neg]
  have hS : symmPart ψ = fun x y => (1 / 2 : ℂ) * ψ x y + (1 / 2 : ℂ) * ψ y x := by
    funext x y
    simp only [symmPart]
    ring
  have hA : antisymmPart ψ = fun x y => (1 / 2 : ℂ) * ψ x y + (-(1 / 2) : ℂ) * ψ y x := by
    funext x y
    simp only [antisymmPart]
    ring
  rw [hS, hA, twoParticleOp_lin_2cd9f4cc, twoParticleOp_lin_2cd9f4cc, hswap]
  constructor
  · module
  · module

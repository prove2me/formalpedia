-- Prove2me | solution 1 for PeresTerno.outcome_probabilities_distribution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:02:37.730989+00:00
-- url     : https://prove2.me/submissions/244f32fd-7611-4757-8b49-c6cc23f1c268

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

open Matrix PeresTerno ComplexOrder in
theorem solution {d e α : Type*} [Fintype d] [Fintype e] [Fintype α]
    {ι : α → Type*} [∀ μ, Fintype (ι μ)] [DecidableEq d]
    (A : ∀ μ, ι μ → Matrix e d ℂ) (hA : ∑ μ, povmElement (A μ) = 1)
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ) :
    (∀ μ, 0 ≤ trace (krausUpdate (A μ) ρ)) ∧ ∑ μ, trace (krausUpdate (A μ) ρ) = 1 := by
  refine ⟨fun μ => ?_, ?_⟩
  · apply PosSemidef.trace_nonneg
    unfold krausUpdate
    exact posSemidef_sum _ fun m _ => hρ.1.mul_mul_conjTranspose_same (A μ m)
  · have key : ∀ μ, trace (krausUpdate (A μ) ρ) = trace (povmElement (A μ) * ρ) := by
      intro μ
      unfold krausUpdate povmElement
      rw [trace_sum, Finset.sum_mul, trace_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      exact trace_mul_cycle _ _ _
    simp_rw [key]
    rw [← trace_sum, ← Finset.sum_mul, hA, Matrix.one_mul]
    exact hρ.2

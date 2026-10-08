-- Prove2me | solution 1 for PeresTerno.commuting_kraus_sum_eq_trace_povm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:26:54.85598+00:00
-- url     : https://prove2.me/submissions/efef818f-c1fe-4b5c-8213-9818939bb4a5

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

open Matrix PeresTerno in
theorem solution {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hAB : ∀ m n, Commute (A m) (B n)) (ρ : Matrix d d ℂ) :
    trace (∑ m, ∑ n, B n * A m * ρ * (A m)ᴴ * (B n)ᴴ)
      = trace (povmElement A * ∑ n, B n * ρ * (B n)ᴴ) := by
  have key : ∀ m n, B n * A m * ρ * (A m)ᴴ * (B n)ᴴ
      = A m * (B n * ρ * (B n)ᴴ) * (A m)ᴴ := by
    intro m n
    have h1 : B n * A m = A m * B n := (hAB m n).eq.symm
    have h2 : (A m)ᴴ * (B n)ᴴ = (B n)ᴴ * (A m)ᴴ := by
      rw [← conjTranspose_mul, ← conjTranspose_mul, h1]
    calc B n * A m * ρ * (A m)ᴴ * (B n)ᴴ
        = (B n * A m) * ρ * ((A m)ᴴ * (B n)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = A m * (B n * ρ * (B n)ᴴ) * (A m)ᴴ := by
          rw [h1, h2]; simp only [Matrix.mul_assoc]
  simp_rw [key]
  have h3 : ∀ m, ∑ n, A m * (B n * ρ * (B n)ᴴ) * (A m)ᴴ
      = A m * (∑ n, B n * ρ * (B n)ᴴ) * (A m)ᴴ := by
    intro m
    rw [Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [h3]
  unfold povmElement
  rw [trace_sum, Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [trace_mul_comm, Matrix.mul_assoc]

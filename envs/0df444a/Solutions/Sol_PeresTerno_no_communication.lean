-- Prove2me | solution 1 for PeresTerno.no_communication
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:09:40.831121+00:00
-- url     : https://prove2.me/submissions/02525ac3-849b-469f-b3ea-601eeb760710

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

open Matrix PeresTerno in
theorem solution {d α β : Type*} [Fintype d] [DecidableEq d] [Fintype α] [Fintype β]
    {ι : α → Type*} [∀ μ, Fintype (ι μ)] {κ : β → Type*} [∀ ν, Fintype (κ ν)]
    (A : ∀ μ, ι μ → Matrix d d ℂ) (B : ∀ ν, κ ν → Matrix d d ℂ)
    (hA : ∑ μ, povmElement (A μ) = 1) (hB : ∑ ν, povmElement (B ν) = 1)
    (hAB : ∀ μ m ν n, Commute (A μ m) (B ν n))
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ) (ν : β) :
    ∑ μ, trace (∑ m, ∑ n, B ν n * A μ m * ρ * (A μ m)ᴴ * (B ν n)ᴴ)
      = trace (∑ n, B ν n * ρ * (B ν n)ᴴ) := by
  have key : ∀ μ m n, trace (B ν n * A μ m * ρ * (A μ m)ᴴ * (B ν n)ᴴ)
      = trace ((A μ m)ᴴ * A μ m * (B ν n * ρ * (B ν n)ᴴ)) := by
    intro μ m n
    have h1 : B ν n * A μ m = A μ m * B ν n := ((hAB μ m ν n).eq).symm
    have h2 : (A μ m)ᴴ * (B ν n)ᴴ = (B ν n)ᴴ * (A μ m)ᴴ := by
      rw [← conjTranspose_mul, ← conjTranspose_mul, h1]
    have h3 : B ν n * A μ m * ρ * (A μ m)ᴴ * (B ν n)ᴴ
        = A μ m * (B ν n * ρ * (B ν n)ᴴ) * (A μ m)ᴴ := by
      rw [h1, Matrix.mul_assoc (A μ m * B ν n * ρ) (A μ m)ᴴ, h2]
      simp only [Matrix.mul_assoc]
    rw [h3, trace_mul_comm, ← Matrix.mul_assoc]
  rw [show trace (∑ n, B ν n * ρ * (B ν n)ᴴ)
      = trace ((∑ μ, povmElement (A μ)) * ∑ n, B ν n * ρ * (B ν n)ᴴ) by
        rw [hA, Matrix.one_mul]]
  simp only [povmElement, Finset.sum_mul, Matrix.mul_sum, trace_sum, key]

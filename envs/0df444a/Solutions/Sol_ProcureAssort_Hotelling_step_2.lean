-- Prove2me | solution 1 for ProcureAssort.Hotelling.step_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:14:36.691866+00:00
-- url     : https://prove2.me/submissions/ca46d7f3-d87e-4051-86e0-a360e8cd6f80

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

open ProcureAssort.Hotelling

theorem solution
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (a : Profile Θ → Fin n → ℝ)
    (h14 : ∀ θ : Profile Θ, ∀ j ∈ activeSet Θ f ℓ δ θ,
      ∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j = 0) :
    ∑ θ : Profile Θ, ∑ i ∈ activeSet Θ f ℓ δ θ,
      a θ i * ∑ j ∈ activeSet Θ f ℓ δ θ, pathA (activeSet Θ f ℓ δ θ) i j * vvec Θ f θ j = 0 := by
  refine Finset.sum_eq_zero fun θ _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  have := h14 θ j hj
  calc ∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * (pathA (activeSet Θ f ℓ δ θ) i j * vvec Θ f θ j)
      = (∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j) * vvec Θ f θ j := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [this, zero_mul]

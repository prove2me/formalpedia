-- Prove2me | solution 1 for RadGauss.Kernel.feature_map_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:59:56.651371+00:00
-- url     : https://prove2.me/submissions/6f44087e-937f-4ccc-9fa7-7f35165ef444

import Mathlib
import Definitions.Def_RadGauss_Kernel_KernelClass



namespace RadGauss.Kernel

theorem fm_core {X H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (k : X → X → ℝ) (hk : IsKernel k) (Φ : X → H)
    (hΦ : ∀ x₁ x₂, k x₁ x₂ = inner ℝ (Φ x₁) (Φ x₂)) (B : ℝ) (hB : 0 ≤ B) :
    (∀ (m : ℕ) (x : Fin m → X) (α : Fin m → ℝ),
        ‖∑ i, α i • Φ (x i)‖ ^ 2 = ∑ i, ∑ j, α i * α j * k (x i) (x j)) ∧
      kernelClass k B ⊆ {f | ∃ w : H, ‖w‖ ≤ B ∧ f = fun x => inner ℝ w (Φ x)} := by
  have h1 : ∀ (m : ℕ) (x : Fin m → X) (α : Fin m → ℝ),
      ‖∑ i, α i • Φ (x i)‖ ^ 2 = ∑ i, ∑ j, α i * α j * k (x i) (x j) := by
    intro m x α
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, hΦ]
    simp only [conj_trivial]; ring
  refine ⟨h1, ?_⟩
  rintro f ⟨m, c, α, hle, rfl⟩
  refine ⟨∑ i, α i • Φ (c i), ?_, ?_⟩
  · have := h1 m c α
    have h2 : ‖∑ i, α i • Φ (c i)‖ ^ 2 ≤ B ^ 2 := this ▸ hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).1 h2
  · funext y
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hΦ, real_inner_comm]
    simp

end RadGauss.Kernel

open RadGauss.Kernel


theorem solution {X H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (k : X → X → ℝ) (hk : IsKernel k) (Φ : X → H)
    (hΦ : ∀ x₁ x₂, k x₁ x₂ = inner ℝ (Φ x₁) (Φ x₂)) (B : ℝ) (hB : 0 ≤ B) :
    (∀ (m : ℕ) (x : Fin m → X) (α : Fin m → ℝ),
        ‖∑ i, α i • Φ (x i)‖ ^ 2 = ∑ i, ∑ j, α i * α j * k (x i) (x j)) ∧
      kernelClass k B ⊆ {f | ∃ w : H, ‖w‖ ≤ B ∧ f = fun x => inner ℝ w (Φ x)} := by
  exact fm_core k hk Φ hΦ B hB

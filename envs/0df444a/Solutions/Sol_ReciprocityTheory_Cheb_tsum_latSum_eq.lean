-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tsum_latSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:59.739211+00:00
-- url     : https://prove2.me/submissions/19098f92-f3f1-45c0-86ab-5f74d603fb35

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open ReciprocityTheory ReciprocityTheory.Cheb
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (g : V → ℂ) (hg : Summable fun α : Λ₀ => g α) :
    ∑' α : Λ₀, c' α * g α = ∑' l : Λ', ∑ β ∈ reps, c' β * (g (l + β) - g l) := by
  set e := latSumEquiv Λ₀ Λ' hle reps hmem hcover huniq
  have hc : ∀ α : Λ₀, ‖c' α‖ ≤ ∑ β ∈ reps, ‖c' β‖ := by
    rintro ⟨α, hα⟩
    obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
    rw [hper l hl β hβ]
    exact Finset.single_le_sum (f := fun β => ‖c' β‖) (fun _ _ => norm_nonneg _) hβ
  have hcg : Summable fun α : Λ₀ => c' α * g α := by
    refine summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_)
      ((summable_norm_iff.mpr hg).mul_left (∑ β ∈ reps, ‖c' β‖)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc α) (norm_nonneg _)
  have hs : Summable fun p : Λ' × reps => c' (e p) * g (e p) := (e.summable_iff).mpr hcg
  rw [← e.tsum_eq, hs.tsum_prod]
  refine tsum_congr fun l => ?_
  rw [tsum_fintype]
  have h1 : ∀ β : reps, (fun α : Λ₀ => c' α * g α) (e (l, β)) = c' β * g (l + β) := by
    rintro ⟨β, hβ⟩
    show c' ((l : V) + β) * g ((l : V) + β) = _
    rw [hper l l.2 β hβ]
  simp only [h1]
  rw [Finset.sum_coe_sort reps (fun β => c' β * g (l + β))]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmean, zero_mul, sub_zero]
end ReciprocityTheory.Cheb

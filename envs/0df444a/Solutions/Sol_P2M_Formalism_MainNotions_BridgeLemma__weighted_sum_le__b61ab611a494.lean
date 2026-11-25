-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le__b61ab611a494
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:31.055928+00:00
-- url     : https://prove2.me/submissions/6f7fdf45-1039-4999-8dea-8c904408fc97

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsFibres
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le_c02fd4b1571a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → ∀ S' : Finset Pr, S' ⊆ S →
      (∀ p ∈ S', c₁ p = x ∧ c₂ p = y) → ∑ p ∈ S', w p ≤ M * N x y)
    (hN : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₁ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ)
    (hΦ₂ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₂ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  classical
  refine weighted_sum_le S w a₁ a₂ c₁ c₂ M R Φ N α φ hM hR hw ha₁ ha₂ hα₁ hα₂ ?_ ?_ hα0 hφ0 ?_ ?_
  · intro x hx y hy
    exact hcount x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy) _ (Finset.filter_subset _ _)
      fun p hp => (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    exact hN x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy)
  · exact hΦ₁ _ fun x hx => Finset.mem_image.1 hx
  · exact hΦ₂ _ fun x hx => Finset.mem_image.1 hx
end Formalism.MainNotions.BridgeLemma₂

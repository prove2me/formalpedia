-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le_c02fd4b1571a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:07.180676+00:00
-- url     : https://prove2.me/submissions/1cd9cdd0-5362-4a5b-b27d-e49a1683da83

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsFibres
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_fibres_f4031f5b82c0

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
open Classical
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p ≤ M * N x y)
    (hN : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∑ x ∈ S.image c₁, φ x ≤ Φ) (hΦ₂ : ∑ y ∈ S.image c₂, φ y ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  rw [rows_fibres S c₁ c₂]
  have hΦ0 : 0 ≤ Φ := le_trans (Finset.sum_nonneg fun x _ => hφ0 x) hΦ₁
  calc ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
      ≤ ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, M * (R * (φ x * φ y)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        calc ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
            ≤ ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (α x * α y) := by
              refine Finset.sum_le_sum fun p hp => ?_
              obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hp
              refine mul_le_mul_of_nonneg_left ?_ (hw p hpS)
              exact mul_le_mul (h1 ▸ hα₁ p hpS) (h2 ▸ hα₂ p hpS) (ha₂ p hpS) (hα0 x)
          _ = (∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p) * (α x * α y) := by rw [Finset.sum_mul]
          _ ≤ (M * N x y) * (α x * α y) :=
              mul_le_mul_of_nonneg_right (hcount x hx y hy) (mul_nonneg (hα0 x) (hα0 y))
          _ = M * (N x y * (α x * α y)) := by ring
          _ ≤ M * (R * (φ x * φ y)) := mul_le_mul_of_nonneg_left (hN x hx y hy) hM
    _ = M * (R * ((∑ x ∈ S.image c₁, φ x) * ∑ y ∈ S.image c₂, φ y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ M * (R * Φ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) hM
        rw [sq]
        exact mul_le_mul hΦ₁ hΦ₂ (Finset.sum_nonneg fun x _ => hφ0 x) hΦ0
end Formalism.MainNotions.BridgeLemma₂

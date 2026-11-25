-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmu_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:40:04.192573+00:00
-- url     : https://prove2.me/submissions/18ce98e7-b488-4fdc-9a7d-e4c0b19531ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_pos_complexPadic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_lt_one_complexPadic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_shape


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact norm_nonneg _
  obtain ⟨m, a, -, b, -, ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1 ⊢
  have hm : 1 ≤ m := by
    by_contra hc
    have hm0 : m ≤ 0 := by omega
    have := one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0
    linarith
  calc ‖(l : ℂ_[l])‖ ^ m ≤ ‖(l : ℂ_[l])‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm
    _ = ‖(l : ℂ_[l])‖ := zpow_one _
end ReciprocityTheory.ChartRestriction.L1

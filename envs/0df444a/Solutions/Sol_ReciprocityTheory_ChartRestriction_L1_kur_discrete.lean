-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kur_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:55:42.934124+00:00
-- url     : https://prove2.me/submissions/b7f432a4-dd41-4661-89e1-f5a93d716323

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_eq_of_norm_sub_lt_max
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_discrete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_approx

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
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero]
    exact norm_nonneg _
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖x‖ hpos
  have heq : ‖x‖ = ‖y‖ := norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hxy (le_max_left _ _))
  rw [heq] at h1 ⊢
  exact kmu_discrete l hy h1
end ReciprocityTheory.ChartRestriction.L1

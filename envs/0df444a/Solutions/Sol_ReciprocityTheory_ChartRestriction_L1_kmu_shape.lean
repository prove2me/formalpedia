-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmu_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:14.503125+00:00
-- url     : https://prove2.me/submissions/7a7e8189-1973-448f-80ac-8de8ee535056

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_frac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_shape

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
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ Kmu l) (hx0 : x ≠ 0) :
    ∃ m : ℤ, ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ x = (l : ℂ_[l]) ^ m * (a / b) := by
  obtain ⟨a, ha, b, hb, hb0, rfl⟩ := kmu_frac l hx
  have ha0 : a ≠ 0 := by rintro rfl; exact hx0 (zero_div b)
  obtain ⟨m, c, hc, u, hu, hc1, hu1, hau⟩ := rmu_shape l ha ha0
  obtain ⟨n, d, hd, v, hv, hd1, hv1, hbv⟩ := rmu_shape l hb hb0
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd1
  refine ⟨(m : ℤ) - n, c * v, mul_mem hc hv, d * u, mul_mem hd hu,
    by rw [norm_mul, hc1, hv1, one_mul], by rw [norm_mul, hd1, hu1, one_mul], ?_⟩
  rw [zpow_sub₀ hl0, zpow_natCast, zpow_natCast]
  have ha' : a = (l : ℂ_[l]) ^ m * c / u := by rw [← hau, mul_div_cancel_right₀ _ hu0]
  have hb' : b = (l : ℂ_[l]) ^ n * d / v := by rw [← hbv, mul_div_cancel_right₀ _ hv0]
  rw [ha', hb']
  field_simp
end ReciprocityTheory.ChartRestriction.L1

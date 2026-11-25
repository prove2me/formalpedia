-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.tch_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:21:09.125487+00:00
-- url     : https://prove2.me/submissions/3ec228b4-0c10-4836-9d56-2130310f362e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TchOfIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_frob_fix_of_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_isIntegral_int_of_rmu
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_le_one_of_integral_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_l_Cl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_near


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
theorem _root_.solution (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) : ∃ ξ ∈ Tch l, ‖δ - ξ‖ < 1 := by
  have hZ := KE.isIntegral_int_of_rmu (l := l) δ hδ
  have h1 : ‖δ‖ ≤ 1 := KE.norm_le_one_of_integral_int δ hZ
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl (l := l)]
    have h1l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ h1l
  obtain ⟨f, hf, hfr⟩ := KE.frob_fix_of_integral l (Fact.out : l.Prime) hl δ hZ
  obtain ⟨ξ, hξ, hd⟩ := tch_near (l := l) δ h1 f hf _ hfr le_rfl
  exact ⟨ξ, hξ, lt_of_le_of_lt hd hfr⟩
end ReciprocityTheory.ChartRestriction.L1

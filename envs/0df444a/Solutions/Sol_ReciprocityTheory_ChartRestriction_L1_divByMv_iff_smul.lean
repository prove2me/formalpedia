-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_iff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:09.893883+00:00
-- url     : https://prove2.me/submissions/bc768ed1-4bba-4591-ba9c-adeb53ee5684

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one

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
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} (hx : x ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x F ↔ ∃ G : MvPowerSeries ι K, IntegralMv G ∧ F = x • G := by
  constructor
  · intro h
    refine ⟨x⁻¹ • F, ?_, by rw [smul_smul, mul_inv_cancel₀ hx, one_smul]⟩
    refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_smul, norm_mul, norm_inv, norm_one,
      inv_mul_le_iff₀ (norm_pos_iff.mpr hx), mul_one]
    exact h d
  · rintro ⟨G, hG, rfl⟩ d
    have h1 := (integralMv_iff_divBy_one G).mp hG d
    rw [norm_one] at h1
    rw [MvPowerSeries.coeff_smul, norm_mul]
    calc ‖x‖ * ‖MvPowerSeries.coeff d G‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖x‖ := mul_one _
end ReciprocityTheory.ChartRestriction.L1

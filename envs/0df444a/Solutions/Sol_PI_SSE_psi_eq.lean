-- Prove2me | solution 1 for PI.SSE.psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:03.972595+00:00
-- url     : https://prove2.me/submissions/5f24616d-2af6-407a-b49a-697532b5d804

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt
import Theorems.Thm_PI_SSE_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) (m n : ℤ) :
    (-1 : ℂ) ^ (m + n + m * n) =
      if ((m : ℂ) * v₁ + n * v₂) / 2 ∈ PI.lat2 v₁ v₂ then 1 else -1 := by
  by_cases hmem : ((m : ℂ) * v₁ + n * v₂) / 2 ∈ PI.lat2 v₁ v₂
  · rw [if_pos hmem]
    unfold PI.lat2 at hmem
    obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.mp hmem
    rw [zsmul_eq_mul, zsmul_eq_mul] at hpq
    obtain ⟨h1, h2⟩ := indep v₁ v₂ h (m - 2 * p) (n - 2 * q) (by push_cast; linear_combination (-2 : ℂ) * hpq)
    obtain rfl : m = 2 * p := by omega
    obtain rfl : n = 2 * q := by omega
    exact Even.neg_one_zpow ⟨p + q + 2 * p * q, by ring⟩
  · rw [if_neg hmem]
    have hodd : Odd (m + n + m * n) := by
      rcases Int.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases Int.even_or_odd n with ⟨b, hb⟩ | ⟨b, hb⟩
      · exfalso
        apply hmem
        unfold PI.lat2
        refine AddSubgroup.mem_closure_pair.mpr ⟨a, b, ?_⟩
        rw [zsmul_eq_mul, zsmul_eq_mul, ha, hb]
        push_cast
        ring
      · exact ⟨2 * a + b + 2 * a * b, by rw [ha, hb]; ring⟩
      · exact ⟨a + 2 * b + 2 * a * b, by rw [ha, hb]; ring⟩
      · exact ⟨2 * a + 2 * b + 2 * a * b + 1, by rw [ha, hb]; ring⟩
    exact hodd.neg_one_zpow
end PI.SSE

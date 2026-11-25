-- Prove2me | solution 1 for PIW.FdPA.inv_mul_between_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:23:56.495632+00:00
-- url     : https://prove2.me/submissions/976e4b56-2a36-4bfc-b920-0965f5e62f00

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {c m m0 ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hm0 : c * m0 = 1)
    (hlo : (1 - ρ) / (1 + ρ) * m0 ≤ m) (hhi : m ≤ (1 + ρ) / (1 - ρ) * m0) :
    (1 - ρ) / (1 + ρ) ≤ 1 / (c * m) ∧ 1 / (c * m) ≤ (1 + ρ) / (1 - ρ) := by
  have hm0pos : 0 < m0 := by nlinarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have h1ρ' : 0 < 1 + ρ := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hlo
  have hcm : 1 / (c * m) = m0 / m := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-m) * hm0
  rw [hcm]
  constructor
  · rw [div_le_div_iff₀ h1ρ' hmpos]
    have h := hhi
    rw [div_mul_eq_mul_div, le_div_iff₀ h1ρ] at h
    linarith
  · rw [div_le_div_iff₀ hmpos h1ρ]
    have h := hlo
    rw [div_mul_eq_mul_div, div_le_iff₀ h1ρ'] at h
    linarith
end PIW.FdPA

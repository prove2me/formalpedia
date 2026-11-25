-- Prove2me | solution 1 for PIW.FdPA.small_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:04.33874+00:00
-- url     : https://prove2.me/submissions/a4e615d3-adf4-49a8-86bb-8139a97001e7

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
theorem _root_.solution {w r rh z : ℝ} (hr0 : 0 ≤ r) (hrw : r ≤ w) (hw : 0 ≤ w) (hrh : 0 ≤ rh)
    (hwrh : w * rh ≤ 1 / 36) (hz0 : 0 ≤ z) (hz : z ≤ rh) : 4 * w * r * z ^ 2 ≤ 1 / 4 := by
  have h1 : w * r ≤ w * w := mul_le_mul_of_nonneg_left hrw hw
  have h2 : z ^ 2 ≤ rh ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have h3 : (w * rh) ^ 2 ≤ (1 / 36) ^ 2 := pow_le_pow_left₀ (mul_nonneg hw hrh) hwrh 2
  have h4 : w * r * z ^ 2 ≤ w * w * rh ^ 2 :=
    mul_le_mul h1 h2 (sq_nonneg z) (mul_nonneg hw hw)
  nlinarith
end PIW.FdPA

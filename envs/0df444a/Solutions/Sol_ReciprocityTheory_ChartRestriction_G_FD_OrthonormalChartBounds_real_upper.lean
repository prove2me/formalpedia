-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.real_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:58.27464+00:00
-- url     : https://prove2.me/submissions/28028237-0be7-4f23-b96c-02b0ea8e12de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealLower2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {ρ α β Q : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 ≤ ρ)
    (hQ : Q * (1 - ρ ^ 2) ≤ (α + ρ * β) ^ 2) :
    2 * Q - (α ^ 2 - β ^ 2) ≤ (1 + ρ) / (1 - ρ) * (α ^ 2 + β ^ 2) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + ρ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith [mul_nonneg hρ0 (sq_nonneg (α - β)), mul_le_mul_of_nonneg_left hQ h2.le]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mjip_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:37.21281+00:00
-- url     : https://prove2.me/submissions/7546975a-b57b-4dad-a52f-3b86167a041d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates

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
theorem _root_.solution {n : ℕ} (p q : Fin n → ℂ) :
    ‖mjip p q‖ ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) := by
  unfold mjip nsq
  calc ‖∑ i, p i * conj (q i)‖ ≤ ∑ i, ‖p i * conj (q i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖p i‖ * ‖q i‖ := by simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

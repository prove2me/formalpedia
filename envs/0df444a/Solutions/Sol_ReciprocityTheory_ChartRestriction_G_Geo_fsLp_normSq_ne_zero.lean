-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fsLp_normSq_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:38.947551+00:00
-- url     : https://prove2.me/submissions/51802f54-b496-47dd-b2e4-403b4738ac76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {z : ι → ℂ} (hz : z ≠ 0) : ‖fsLp ι z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (fsLp_ne_zero hz))
end ReciprocityTheory.ChartRestriction.G.Geo

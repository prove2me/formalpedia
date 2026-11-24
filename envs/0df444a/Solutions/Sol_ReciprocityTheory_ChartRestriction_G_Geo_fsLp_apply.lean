-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fsLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:52.81592+00:00
-- url     : https://prove2.me/submissions/0f169b9e-39df-4305-b916-74663cd81779

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive

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
theorem _root_.solution (z : ι → ℂ) : fsLp ι z = WithLp.toLp 2 z := rfl
end ReciprocityTheory.ChartRestriction.G.Geo

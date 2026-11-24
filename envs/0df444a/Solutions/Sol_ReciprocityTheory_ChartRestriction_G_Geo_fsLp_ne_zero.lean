-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fsLp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:35.16224+00:00
-- url     : https://prove2.me/submissions/f02733d5-82ca-4a41-b1ac-8dfde51204aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_apply

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
theorem _root_.solution {z : ι → ℂ} (hz : z ≠ 0) : fsLp ι z ≠ 0 := by
  rw [fsLp_apply]
  intro h
  apply hz
  have h2 := congrArg (WithLp.ofLp (p := 2)) h
  simpa using h2
end ReciprocityTheory.ChartRestriction.G.Geo

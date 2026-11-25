-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fsMetric_isSemipositive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:22.335802+00:00
-- url     : https://prove2.me/submissions/f33d7e10-ed83-429f-83d9-cc2d5bc4250e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsMetric_isSmooth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_leviForm_fsMetric

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
theorem _root_.solution : IsSemipositive (fsMetric ι) := by
  refine ⟨fsMetric_isSmooth, fun z hz w => ?_⟩
  rw [leviForm_fsMetric hz]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (fsLp ι z) (fsLp ι w)
  have h2 := mul_self_le_mul_self (norm_nonneg _) hcs
  apply div_nonneg
  · nlinarith [h2]
  · positivity
end ReciprocityTheory.ChartRestriction.G.Geo

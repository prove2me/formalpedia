-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.differentiableAt_fsGrad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:10.412197+00:00
-- url     : https://prove2.me/submissions/35460615-a197-43dc-bc16-3bd2b324b5fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_normSq_ne_zero

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
theorem _root_.solution {z : ι → ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fsGrad (ι := ι)) z := by
  show DifferentiableAt ℝ
    (fun y => (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) z
  have h1 : DifferentiableAt ℝ (fun y => (‖fsLp ι y‖ ^ 2)⁻¹) z :=
    (DifferentiableAt.norm_sq ℂ (fsLp ι).differentiableAt).inv (fsLp_normSq_ne_zero hz)
  have h2 : DifferentiableAt ℝ (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) z :=
    (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))).differentiableAt
  exact h1.smul h2
end ReciprocityTheory.ChartRestriction.G.Geo

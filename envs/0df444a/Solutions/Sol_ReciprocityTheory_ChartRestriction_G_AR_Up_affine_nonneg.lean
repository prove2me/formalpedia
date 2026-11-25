-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.affine_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:54.57572+00:00
-- url     : https://prove2.me/submissions/e85710b8-8da2-4445-bcfa-8ab6001322b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CurvNumStatementPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution (α β t t1 : ℝ) (h0 : 0 ≤ α) (h1 : 0 ≤ α + β * t1) (ht : 0 ≤ t) (ht1 : t ≤ t1) :
    0 ≤ α + β * t := by
  rcases le_total 0 β with hb | hb
  · nlinarith [mul_nonneg hb ht]
  · nlinarith [mul_le_mul_of_nonpos_left ht1 hb]
end ReciprocityTheory.ChartRestriction.G.AR.Up

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_Ioi_ofReal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:34.230921+00:00
-- url     : https://prove2.me/submissions/c1422cf9-c617-4295-8293-bb29e584a8aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution (F : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r = ∫⁻ r, ENNReal.ofReal r * F r := by
  rw [← lintegral_indicator measurableSet_Ioi]
  congr 1
  funext r
  by_cases hr : r ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hr]
  · rw [indicator_of_notMem hr, ENNReal.ofReal_of_nonpos (not_lt.mp hr), zero_mul]
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

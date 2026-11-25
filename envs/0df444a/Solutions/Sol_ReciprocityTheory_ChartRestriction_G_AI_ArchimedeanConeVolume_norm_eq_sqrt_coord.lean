-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.norm_eq_sqrt_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:50.650821+00:00
-- url     : https://prove2.me/submissions/794b5a9c-33a2-4368-a12b-c4b5f3fe2760

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
theorem _root_.solution (y : E3) : ‖y‖ = Real.sqrt (y 0 ^ 2 + (y 1 ^ 2 + y 2 ^ 2)) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  ring_nf
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

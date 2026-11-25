-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.toSphere_univ_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:22.101858+00:00
-- url     : https://prove2.me/submissions/f86830cd-b000-4c79-b054-fbc1ec79a2ca

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
theorem _root_.solution : (volume : Measure E3).toSphere univ ≠ 0 :=
  Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

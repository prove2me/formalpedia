-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.measurable_coneFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:18.384801+00:00
-- url     : https://prove2.me/submissions/66f1e1a1-ef33-4009-80c7-a6e8bb09156b

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
theorem _root_.solution {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun p : ℝ × ℝ => coneFun G p.1 p.2) := by
  unfold coneFun
  refine Measurable.ite ?_ (hG.comp ?_) measurable_const
  · exact (measurableSet_lt (f := fun _ : ℝ × ℝ => (0 : ℝ)) (g := fun p : ℝ × ℝ => p.1 ^ 2 + p.2)
      measurable_const (by fun_prop)).inter (measurableSet_lt (g := fun _ : ℝ × ℝ => (1 : ℝ))
      (f := fun p : ℝ × ℝ => p.1 ^ 2 + p.2) (by fun_prop) measurable_const)
  · fun_prop
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

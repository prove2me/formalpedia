-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.reflection_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:14.456319+00:00
-- url     : https://prove2.me/submissions/c21f3f2b-47aa-4368-a435-ed9c855928dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open MeasureTheory
variable {u : E3} {f : ℝ → ℝ}
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {a c : E3} (h : inner ℝ a c = 0) : (ℝ ∙ a)ᗮ.reflection c = c := by
  have hc : c ∈ (ℝ ∙ a)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.2 h
  exact Submodule.reflection_mem_subspace_eq_self hc
end ReciprocityTheory.ChartRestriction.G.AI

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.qf_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:26.233853+00:00
-- url     : https://prove2.me/submissions/16612614-f524-42b5-b76c-26162c28e1d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]
variable {B : LinearMap.BilinForm 𝕜 W}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hB : ∀ x y, B x y = B y x) (x y : W) : qf B (x + y) = qf B x + B x y + qf B y := by
  simp only [qf, map_add, LinearMap.add_apply, hB y x]; ring
end ReciprocityTheory.ChartRestriction.G.DVR

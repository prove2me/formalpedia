-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.qf_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:26.43706+00:00
-- url     : https://prove2.me/submissions/ace42a38-fc46-4e7c-a0b5-e1a15cd62b78

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
theorem _root_.solution (c : 𝕜) (x : W) : qf B (c • x) = c ^ 2 * qf B x := by
  simp only [qf, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
end ReciprocityTheory.ChartRestriction.G.DVR

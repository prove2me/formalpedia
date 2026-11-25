-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG.amgm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:12.526179+00:00
-- url     : https://prove2.me/submissions/8f953d25-5c1e-41a0-9a9e-3d06ebcfd9c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
theorem _root_.solution {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by
  have h : 0 ≤ (x - k * y) ^ 2 / k := by positivity
  have e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2 := by
    field_simp
    ring
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

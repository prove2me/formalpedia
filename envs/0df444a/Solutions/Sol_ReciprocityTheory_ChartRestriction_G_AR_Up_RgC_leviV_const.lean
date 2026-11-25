-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgC.leviV_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:40.086189+00:00
-- url     : https://prove2.me/submissions/8cddf98e-8d27-4b4a-aaf3-6268bb960f2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
theorem _root_.solution (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => (c : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => (c : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

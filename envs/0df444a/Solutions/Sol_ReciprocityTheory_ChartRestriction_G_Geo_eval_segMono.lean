-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_segMono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:53.737592+00:00
-- url     : https://prove2.me/submissions/70d53169-9091-4ff3-a0b4-e8498de791fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : eval z (segMono ι i) = segre z i := by
  simp [segMono, segre, map_prod]
end ReciprocityTheory.ChartRestriction.G.Geo

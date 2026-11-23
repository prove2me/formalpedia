-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.unit_finsupp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:07.996998+00:00
-- url     : https://prove2.me/submissions/32f1be62-161f-43cb-a797-3a6d6ef34492

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (e : Unit →₀ ℕ) : e = Finsupp.single () (e ()) := by
  exact Finsupp.ext fun u => by cases u; simp
end ReciprocityTheory.ChartRestriction.G.Sh.PTb

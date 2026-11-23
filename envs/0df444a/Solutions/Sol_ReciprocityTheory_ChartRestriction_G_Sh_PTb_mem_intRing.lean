-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.mem_intRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:07.963719+00:00
-- url     : https://prove2.me/submissions/5cd1aa90-77b6-4270-9735-0d3cc57154e5

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
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {x : C} :
    x ∈ intRing v ↔ IsIntV v x := Iff.rfl
end ReciprocityTheory.ChartRestriction.G.Sh.PTb

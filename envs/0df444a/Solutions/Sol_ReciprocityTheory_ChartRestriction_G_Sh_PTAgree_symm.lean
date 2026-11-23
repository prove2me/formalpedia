-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:44.11049+00:00
-- url     : https://prove2.me/submissions/6db9db61-708f-44c7-95c1-7dbb46d4a9b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Sh
namespace PTAgree
theorem _root_.solution {k : ℕ} {A B : ι → MvPowerSeries τ R} (h : PTAgree k A B) :
    PTAgree k B A := fun i e he => (h i e he).symm
end PTAgree
end ReciprocityTheory.ChartRestriction.G.Sh

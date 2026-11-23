-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:16.852803+00:00
-- url     : https://prove2.me/submissions/4f139a8f-e24d-474b-b8b2-5cf73caa631b

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
theorem _root_.solution {k : ℕ} {A B D : ι → MvPowerSeries τ R} (h : PTAgree k A B)
    (h' : PTAgree k B D) : PTAgree k A D := fun i e he => (h i e he).trans (h' i e he)
end PTAgree
end ReciprocityTheory.ChartRestriction.G.Sh

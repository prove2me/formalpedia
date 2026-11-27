-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:27.648024+00:00
-- url     : https://prove2.me/submissions/286025b4-377d-43ad-b20a-63ec0f83a412

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
theorem _root_.solution {k l : ℕ} {A A' : ι → MvPowerSeries τ R} (h : PTAgree k A A') (hl : l ≤ k) :
    PTAgree l A A' := fun i e he => h i e (lt_of_lt_of_le he hl)
end PTAgree
end ReciprocityTheory.ChartRestriction.G.Sh

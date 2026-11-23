-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:48.964011+00:00
-- url     : https://prove2.me/submissions/46fae7ec-caf7-4a1f-9705-d463db91df4e

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
theorem _root_.solution {A A' : ι → MvPowerSeries τ R} (h : ∀ k, PTAgree k A A') : A = A' :=
  funext fun i => MvPowerSeries.ext fun e => h (e.degree + 1) i e (Nat.lt_succ_self _)
end PTAgree
end ReciprocityTheory.ChartRestriction.G.Sh

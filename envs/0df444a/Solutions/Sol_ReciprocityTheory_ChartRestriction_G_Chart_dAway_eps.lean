-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dAway_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:23.284535+00:00
-- url     : https://prove2.me/submissions/3c9f66f1-430a-4ae4-a9e4-e03a3e414421

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (s : S)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution : dAway s (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by
  ext <;> simp [dAway, dualMapR]
end ReciprocityTheory.ChartRestriction.G.Chart

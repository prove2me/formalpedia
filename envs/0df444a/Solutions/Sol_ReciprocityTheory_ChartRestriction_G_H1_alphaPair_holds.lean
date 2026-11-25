-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.alphaPair_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:43.013424+00:00
-- url     : https://prove2.me/submissions/5a4c277f-600f-4239-b9fb-1bd508aef821

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_sep_core

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution : AlphaPairStatement := by
  intro E _ _ _ H V _ _ _ t P _ α N hN hαN hu _ F _ _ _ Dw I x x' hx hx' hne
  obtain ⟨u, u', hu⟩ := hu
  exact sep_core (H := H) (R := V) (F := F) P.A P.oA Dw I N hN α u u' hαN hu x x' hx hx' hne
end ReciprocityTheory.ChartRestriction.G.H1

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isoPullId_pgen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:59.639483+00:00
-- url     : https://prove2.me/submissions/900e82e8-26fa-4246-842a-b0410e138a8e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gw_isoPullId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {F : X ⟶ X} (hF : F = 𝟙 X) :
    PGen (isoPullId w hF) := by
  intro Y f y j j' k k' hj hj' hk hk'
  subst hF
  rw [gw_isoPullId w rfl f y j k hj hk, gw_isoPullId w rfl f y j' k' hj' hk', Category.comp_id]
  exact gm_isGen hw f y j j' k k' hj hj' hk hk'
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

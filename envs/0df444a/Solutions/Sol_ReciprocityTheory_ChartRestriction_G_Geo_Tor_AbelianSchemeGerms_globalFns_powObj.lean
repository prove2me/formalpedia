-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.globalFns_powObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:04.78942+00:00
-- url     : https://prove2.me/submissions/1c1695b3-5d24-454a-a4c3-03bdfefc1997

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_AbelianSchemeGerms_isAbelianScheme_of_proper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_AbelianSchemeGerms_isAbelianScheme_powObj

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
theorem _root_.solution (hGF : GlobalFnsSt) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    [IsProper G.hom] (n : ℕ) : Function.Bijective (powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (isAbelianScheme_powObj G (isAbelianScheme_of_proper G hG) n)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers.pull_powObj_globalFns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:30.61833+00:00
-- url     : https://prove2.me/submissions/3736025a-d058-4c16-bf39-7b70e8848e1a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrPowers
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_GlobalFunctionsDvrPowers_bijective_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_AbelianSchemeGerms_globalFns_powObj


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
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
theorem _root_.solution (hGF : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (G : Over S) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    [IsProper ((Over.pullback f).obj G).hom] (n : ℕ) :
    Function.Bijective ((Over.pullback f).obj (powObj G n)).hom.appTop.hom := by
  exact bijective_of_iso (pullPowIso f G n)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.globalFns_powObj hGF ((Over.pullback f).obj G)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f := f) (G := G) hG) n)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers

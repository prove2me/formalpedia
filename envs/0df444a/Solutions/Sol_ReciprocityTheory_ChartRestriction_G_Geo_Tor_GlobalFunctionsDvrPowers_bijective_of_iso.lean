-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers.bijective_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:44:55.088557+00:00
-- url     : https://prove2.me/submissions/3c2b50d2-532e-4721-bf5c-4cd9b2b17984

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrPowers

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
theorem _root_.solution {S' : Scheme.{0}} {A B : Over S'} (e : A ≅ B)
    (h : Function.Bijective B.hom.appTop.hom) : Function.Bijective A.hom.appTop.hom := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  rw [hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ h
  refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.left.appTop).hom, fun x => ?_, fun x => ?_⟩
  · show (e.hom.left.appTop ≫ e.inv.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
    simp
  · show (e.inv.left.appTop ≫ e.hom.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.hom_inv_id]
    simp
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers

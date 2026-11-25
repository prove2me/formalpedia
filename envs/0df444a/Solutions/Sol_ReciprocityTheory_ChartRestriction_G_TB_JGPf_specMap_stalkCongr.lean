-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.JGPf.specMap_stalkCongr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:48.766751+00:00
-- url     : https://prove2.me/submissions/f7b02a5b-fb0e-4c79-989c-c2b1ef7d3f3e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue

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
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.JGPf
universe u
namespace ReciprocityTheory.ChartRestriction.G.TB.JGPf
theorem _root_.solution {X : Scheme.{u}} {x y : X} (e : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst e
  simp
end ReciprocityTheory.ChartRestriction.G.TB.JGPf

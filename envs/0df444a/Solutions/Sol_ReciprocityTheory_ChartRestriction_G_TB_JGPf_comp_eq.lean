-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.JGPf.comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:23.096245+00:00
-- url     : https://prove2.me/submissions/9bbb07ad-6344-40ca-ae48-6932041a554b

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
theorem _root_.solution {A B C D : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C) (f g : C ⟶ D) (h : v ≫ f = v ≫ g) :
    (u ≫ v) ≫ f = (u ≫ v) ≫ g := by
  rw [Category.assoc, Category.assoc, h]
end ReciprocityTheory.ChartRestriction.G.TB.JGPf

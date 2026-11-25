-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_pt_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:48.948585+00:00
-- url     : https://prove2.me/submissions/f2750373-a3c3-4f70-bee9-b5b520f35609

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (a : Over.mk x0 ⟶ A) (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left)
    (h1 : pt ≫ (snd (Over.mk x0) A).left = a.left) (h2 : pt ≫ (fst (Over.mk x0) A).left = 𝟙 _) :
    pt = (vtfQ A a).left := by
  have hw : pt ≫ (Over.mk x0 ⊗ A).hom = x0 := by
    rw [← Over.w (fst (Over.mk x0) A), ← Category.assoc, h2, Category.id_comp]
    rfl
  let q : Over.mk x0 ⟶ Over.mk x0 ⊗ A := Over.homMk pt hw
  have hq : q = vtfQ A a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [vtfQ, lift_fst]
      ext
      exact h2
    · simp only [vtfQ, lift_snd]
      ext
      exact h1
  exact congrArg CommaMorphism.left hq
end ReciprocityTheory.ChartRestriction.G.PullbackSections

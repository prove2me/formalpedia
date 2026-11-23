-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.psi_tr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:47.931862+00:00
-- url     : https://prove2.me/submissions/94c7a075-3e3c-4af4-a777-3d1d0a7f988e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_snd

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (psiO hp τ hτ).left ≫ (translPt G x₀).left = (translPt A x).left ≫ φ := by
  have e₁ : translPt G x₀ = (fst T₀ G ≫ x₀) * snd T₀ G := rfl
  have e₂ : translPt A x = (fst T A ≫ x) * snd T A := rfl
  rw [← Over.comp_left, e₁, MonObj.comp_mul, e₂]
  refine hp.2 _ _ _ _ _ ?_ ?_
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, psi_fst, Category.assoc, hx, Over.comp_left, Category.assoc]
  · rw [Over.comp_left, psi_snd]
end ReciprocityTheory.ChartRestriction.G.H1

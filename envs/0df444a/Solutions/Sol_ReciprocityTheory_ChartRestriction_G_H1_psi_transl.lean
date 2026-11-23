-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.psi_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:33.979897+00:00
-- url     : https://prove2.me/submissions/65a19a1b-57df-4f37-a4f7-fb13543b2a9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_tr

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
    (translT A x).left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ (translT G x₀).left := by
  let m : Over.mk ((T ⊗ A).hom ≫ f) ⟶ Over.mk ((T ⊗ A).hom ≫ f) :=
    Over.homMk (translT A x).left (by
      show (translT A x).left ≫ (T ⊗ A).hom ≫ f = (T ⊗ A).hom ≫ f
      rw [← Category.assoc, Over.w (translT A x)])
  have key : m ≫ psiO hp τ hτ = psiO hp τ hτ ≫ translT G x₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [psiO, lift_fst]
        show (translT A x).left ≫ (fst T A).left ≫ τ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_fst]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [translT, lift_fst, Over.comp_left, psi_fst]
      simpa only [Category.assoc] using e1.trans e2.symm
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [psiO, lift_snd]
        show (translT A x).left ≫ (snd T A).left ≫ φ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_snd]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [translT, lift_snd, Over.comp_left, psi_tr hp τ hτ x x₀ hx]
      simpa only [Category.assoc] using e1.trans e2.symm
  exact congrArg CommaMorphism.left key
end ReciprocityTheory.ChartRestriction.G.H1

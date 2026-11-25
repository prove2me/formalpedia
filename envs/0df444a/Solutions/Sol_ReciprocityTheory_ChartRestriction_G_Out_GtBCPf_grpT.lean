-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.grpT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:30.385809+00:00
-- url     : https://prove2.me/submissions/81ffb856-0582-430a-8abd-6f9a88bf07ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
section Maps
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
private lemma left_mul_congr_lemma {Z W : Scheme.{0}} {M : Over Z} [GrpObj M] {a b : W ⟶ Z}
    (hab : a = b) (u v : Over.mk a ⟶ M) (u' v' : Over.mk b ⟶ M)
    (hu : u.left = u'.left) (hv : v.left = v'.left) : (u * v).left = (u' * v').left := by
  subst hab
  rw [Over.OverMorphism.ext hu, Over.OverMorphism.ext hv]
variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
variable (i : splitTorus S X ⟶ G)
end Maps
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution : IsGrpPullback (splitTorus S' X) (splitTorus S X) f (hT f X) := by
  have hz : f ≫ Semi.toZ S = Semi.toZ S' := specULiftZIsTerminal.hom_ext _ _
  have hTf : hT f X ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) =
      pullback.fst (splitTorusAff _ X).hom (Semi.toZ S') := by
    unfold hT
    exact pullback.lift_fst _ _ _
  have gS := isGrpPullback_pullback (splitTorusAff _ X) (Semi.toZ S)
  have gS' := isGrpPullback_pullback (splitTorusAff _ X) (Semi.toZ S')
  unfold IsGrpPullback
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ (hT_snd f X) gS.1
    rw [hTf, hz]
    exact gS'.1
  · intro T x y x₀ y₀ hx hy
    refine gS.1.hom_ext ?_ ?_
    · let u : Over.mk ((Over.mk (T.hom ≫ f)).hom ≫ Semi.toZ S) ⟶ splitTorusAff _ X :=
        Over.homMk (x₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S))
          (specULiftZIsTerminal.hom_ext _ _)
      let v : Over.mk ((Over.mk (T.hom ≫ f)).hom ≫ Semi.toZ S) ⟶ splitTorusAff _ X :=
        Over.homMk (y₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S))
          (specULiftZIsTerminal.hom_ext _ _)
      let u' : Over.mk (T.hom ≫ Semi.toZ S') ⟶ splitTorusAff _ X :=
        Over.homMk (x.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S'))
          (specULiftZIsTerminal.hom_ext _ _)
      let v' : Over.mk (T.hom ≫ Semi.toZ S') ⟶ splitTorusAff _ X :=
        Over.homMk (y.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S'))
          (specULiftZIsTerminal.hom_ext _ _)
      have e1 := gS.2 (Over.mk (T.hom ≫ f)) x₀ y₀ u v rfl rfl
      have e2 := gS'.2 T x y u' v' rfl rfl
      have e3 : (u * v).left = (u' * v').left := by
        refine left_mul_congr_lemma (specULiftZIsTerminal.hom_ext _ _) u v u' v' ?_ ?_
        · show x₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) =
            x.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')
          rw [hx]
          exact (Category.assoc _ _ _).trans (congrArg (fun g => x.left ≫ g) hTf)
        · show y₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) =
            y.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')
          rw [hy]
          exact (Category.assoc _ _ _).trans (congrArg (fun g => y.left ≫ g) hTf)
      exact e1.symm.trans (e3.trans (e2.trans ((congrArg (fun g => (x * y).left ≫ g) hTf).symm.trans
        (Category.assoc _ _ _).symm)))
    · calc (x₀ * y₀).left ≫ (splitTorus S X).hom = T.hom ≫ f := Over.w (x₀ * y₀)
        _ = ((x * y).left ≫ (splitTorus S' X).hom) ≫ f := by rw [Over.w (x * y)]
        _ = (x * y).left ≫ hT f X ≫ (splitTorus S X).hom := by rw [hT_snd, Category.assoc]
        _ = ((x * y).left ≫ hT f X) ≫ (splitTorus S X).hom := (Category.assoc _ _ _).symm
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

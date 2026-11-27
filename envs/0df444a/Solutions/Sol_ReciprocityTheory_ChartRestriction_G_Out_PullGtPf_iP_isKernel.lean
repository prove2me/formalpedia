-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.iP_isKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:39:45.860313+00:00
-- url     : https://prove2.me/submissions/6a060805-fc74-4e33-9dc7-e9bb3a5c2394

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_qP_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_qP_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_grpT
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_toUnit_left__942dca687bf8
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_IsGrpPullback_one_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_iP_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
open Semi Geo.Tor
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)
variable {φ hφ e}
variable (hφ) {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom] (xe : D'.X ≃+ D.X)
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom] {e : ℕ} (g : GtCoord I D e G)
namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
theorem _root_.solution : IsPullback (iP hφ xe bc g) (toUnit _) (qP hφ eB bc g)
    (η[thickObj R' I' e D'.P.A]) := by
  have s2 : IsPullback g.i.left (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).hom
      g.q.left (η[thickObj R I e D.P.A]).left := by
    have := g.isKernel.map (Over.forget _)
    simpa [toUnit_left'] using this
  have big := (grpT hφ e xe).1.paste_horiz s2
  have hη := IsGrpPullback.one_left (grpB hφ e eB)
  rw [← iP_h hφ xe bc g, ← hη] at big
  have p : (iP hφ xe bc g).left ≫ (qP hφ eB bc g).left =
      (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).hom ≫
        (η[thickObj R' I' e D'.P.A]).left := by
    apply (grpB hφ e eB).1.hom_ext
    · rw [Category.assoc, qP_h, ← Category.assoc, iP_h, Category.assoc, s2.w, Category.assoc, hη,
        ← Category.assoc, ← Category.assoc]
      congr 1
      exact pullback.lift_snd _ _ _
    · rw [Category.assoc, Over.w (qP hφ eB bc g), Over.w (iP hφ xe bc g), Category.assoc,
        Over.w (η[thickObj R' I' e D'.P.A])]
      simp
  have H := IsPullback.of_right big p (qP_sq hφ eB bc g)
  refine IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext ?_) ?_
  · simpa [toUnit_left'] using p
  · simpa [toUnit_left'] using H
end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf

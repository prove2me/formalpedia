-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.w_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:57.768086+00:00
-- url     : https://prove2.me/submissions/9449f1f1-26e1-463a-9db3-0f412f58d35b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pull_g_res
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Flat
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(X, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom (u : Γ(X, U))) =
    (X.presheaf.map ((homOfLE h2).op ≫ (homOfLE h1).op)).hom (u : Γ(X, U))
  rw [Functor.map_comp]
  rfl
end Flat
section NZ
variable {Y : Scheme.{0}}
end NZ
section Main
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
end Main
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (a a' : L₂.ι) (b b' : L₁.ι) {V : Y.Opens}
    (h : V ≤ ((L₂.pull f₂).U (fun _ => a) ⊓ (L₁.pull f₁).U (fun _ => b)) ⊓
      ((L₂.pull f₂).U (fun _ => a') ⊓ (L₁.pull f₁).U (fun _ => b'))) :
    res (h.trans inf_le_left) (w.s (fun _ => a, fun _ => b)) =
      tr L₂ V f₂ a a' * (tr L₁ V f₁ b b')⁻¹ * res (h.trans inf_le_right) (w.s (fun _ => a', fun _ => b')) := by
  have e := hw (fun _ => a, fun _ => b) (fun _ => a', fun _ => b')
  have e' : res (inf_le_left : ((L₂.pull f₂).U (fun _ => a) ⊓ (L₁.pull f₁).U (fun _ => b)) ⊓
        ((L₂.pull f₂).U (fun _ => a') ⊓ (L₁.pull f₁).U (fun _ => b')) ≤ _) (w.s (fun _ => a, fun _ => b)) =
      (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          ((L₂.pull f₂).g (fun _ => a) (fun _ => a')) *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
          ((L₁.pull f₁).g (fun _ => b) (fun _ => b')))⁻¹) *
      res (inf_le_right : _ ⊓ _ ≤ _) (w.s (fun _ => a', fun _ => b')) := e
  refine (res_res_lemma h inf_le_left _).symm.trans ?_
  refine (congrArg (res h) e').trans ?_
  refine ((res h).map_mul _ _).trans ?_
  refine (congrArg (fun t => t * _) ((res h).map_mul _ _)).trans ?_
  refine (congrArg (fun t => _ * t * _) ((res h).map_inv _)).trans ?_
  simp only [res_res_lemma]
  simp only [pull_g_res]
  exact congrArg (fun t => _ * t) (res_res_lemma h _ _)
end ReciprocityTheory.ChartRestriction.G.DVR

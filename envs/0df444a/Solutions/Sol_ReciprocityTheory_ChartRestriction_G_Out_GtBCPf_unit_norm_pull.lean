-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.unit_norm_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:09:13.847503+00:00
-- url     : https://prove2.me/submissions/b6f77508-fd63-4d30-9eb0-969bc270e471

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
private lemma app_res_app_res_lemma {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (O : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hO : O ≤ f ⁻¹ᵁ V) (hO' : O ≤ (f ≫ g) ⁻¹ᵁ U) :
    g.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ f.app V ≫ X.presheaf.map (homOfLE hO).op =
      (f ≫ g).app U ≫ X.presheaf.map (homOfLE hO').op := by
  first
    | rw [Scheme.Hom.naturality_assoc]
    | rw [← Scheme.Hom.naturality_assoc]
  rw [← Functor.map_comp, ← Category.assoc]
  rfl
private lemma res_app_res_lemma_2 {X Y : Scheme.{0}} (f : X ⟶ Y) (V₁ V : Y.Opens) (O : X.Opens)
    (hV : V₁ ≤ V) (hO : O ≤ f ⁻¹ᵁ V₁) (hO' : O ≤ f ⁻¹ᵁ V) :
    Y.presheaf.map (homOfLE hV).op ≫ f.app V₁ ≫ X.presheaf.map (homOfLE hO).op =
      f.app V ≫ X.presheaf.map (homOfLE hO').op := by
  first
    | rw [Scheme.Hom.naturality_assoc]
    | rw [← Scheme.Hom.naturality_assoc]
  rw [← Functor.map_comp]
  rfl
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)
attribute [local instance] SplitExt.free SplitExt.finite
variable {G : Over S} [GrpObj G] (d : E.GtDatum G)
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
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution {S₁ S₂ Y Z : Scheme.{0}} (e₁ : S₁ ⟶ Y) (e₂ : S₂ ⟶ Z) (a : Z ⟶ Y) (ff : S₂ ⟶ S₁)
    (he : e₂ ≫ a = ff ≫ e₁) {W : Y.Opens} (u : Γ(Y, W)ˣ) {W' : Z.Opens} (hW' : W' ≤ a ⁻¹ᵁ W)
    {V : S₁.Opens} (r : Γ(S₁, V)ˣ) {V' : S₂.Opens} (hV' : V' ≤ ff ⁻¹ᵁ V)
    (h : res (inf_le_left : e₁ ⁻¹ᵁ W ⊓ V ≤ e₁ ⁻¹ᵁ W) (pullU e₁ W u) *
      res (inf_le_right : e₁ ⁻¹ᵁ W ⊓ V ≤ V) r = 1) :
    res (inf_le_left : e₂ ⁻¹ᵁ W' ⊓ V' ≤ e₂ ⁻¹ᵁ W') (pullU e₂ W' (res hW' (pullU a W u))) *
      res (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V') (res hV' (pullU ff V r)) = 1 := by
  have p1 : e₂ ⁻¹ᵁ W' ⊓ V' ≤ (e₂ ≫ a) ⁻¹ᵁ W :=
    inf_le_left.trans ((TopologicalSpace.Opens.map e₂.base).map (homOfLE hW')).le
  have p2 : e₂ ⁻¹ᵁ W' ⊓ V' ≤ (ff ≫ e₁) ⁻¹ᵁ W := by rw [← he]; exact p1
  have hq : e₂ ⁻¹ᵁ W' ⊓ V' ≤ ff ⁻¹ᵁ V :=
    inf_le_right.trans hV'
  have hO : e₂ ⁻¹ᵁ W' ⊓ V' ≤ ff ⁻¹ᵁ (e₁ ⁻¹ᵁ W ⊓ V) := by
    show _ ≤ ff ⁻¹ᵁ (e₁ ⁻¹ᵁ W) ⊓ ff ⁻¹ᵁ V
    exact le_inf p2 hq
  have hC : ∀ (g₁ g₂ : S₂ ⟶ Y) (_ : g₁ = g₂) (p : e₂ ⁻¹ᵁ W' ⊓ V' ≤ g₁ ⁻¹ᵁ W)
      (q : e₂ ⁻¹ᵁ W' ⊓ V' ≤ g₂ ⁻¹ᵁ W),
      g₁.app W ≫ S₂.presheaf.map (homOfLE p).op = g₂.app W ≫ S₂.presheaf.map (homOfLE q).op := by
    intro g₁ g₂ hg p q
    subst hg
    rfl
  have hA := app_res_app_res_lemma e₂ a W W' (e₂ ⁻¹ᵁ W' ⊓ V') hW' inf_le_left p1
  have hB := app_res_app_res_lemma ff e₁ W (e₁ ⁻¹ᵁ W ⊓ V) (e₂ ⁻¹ᵁ W' ⊓ V') inf_le_left hO p2
  have hAB := hA.trans ((hC _ _ he p1 p2).trans hB.symm)
  have hD := res_app_res_lemma_2 ff (e₁ ⁻¹ᵁ W ⊓ V) V (e₂ ⁻¹ᵁ W' ⊓ V') inf_le_right hO hq
  have hE : ff.app V ≫ S₂.presheaf.map (homOfLE hV').op ≫
      S₂.presheaf.map (homOfLE (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V')).op =
      ff.app V ≫ S₂.presheaf.map (homOfLE hq).op := by
    rw [← Functor.map_comp]
    rfl
  have key := congrArg (fun t => res hO (pullU ff _ t)) h
  simp only [map_mul, map_one] at key
  refine Eq.trans ?_ key
  congr 1
  · ext
    have hu := congrArg (fun φ => φ.hom (u : Γ(Y, W))) hAB
    simpa [res, pullU] using hu
  · ext
    have hr := congrArg (fun φ => φ.hom (r : Γ(S₁, V))) (hE.trans hD.symm)
    simpa [res, pullU] using hr
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

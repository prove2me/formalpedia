-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.equivPullL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:33.505934+00:00
-- url     : https://prove2.me/submissions/36d114e4-26bb-4886-a3ac-e6ba91db04ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_gmRP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution {T₁ T₂ Y Z P₁ P₂ : Scheme.{0}} (act₁ s₁ : P₁ ⟶ Y) (f₁ : P₁ ⟶ T₁)
    (act₂ s₂ : P₂ ⟶ Z) (f₂ : P₂ ⟶ T₂) (b : P₂ ⟶ P₁) (a : Z ⟶ Y) (h : T₂ ⟶ T₁)
    (W : Y.Opens) (u : Γ(Y, W)ˣ) (W' : Z.Opens) (hW' : W' ≤ a ⁻¹ᵁ W)
    (c : Γ(T₁, ⊤)ˣ) (c' : Γ(T₂, ⊤)ˣ)
    (hc : res (fun _ _ => trivial : (⊤ : T₂.Opens) ≤ h ⁻¹ᵁ ⊤) (pullU h ⊤ c) = c')
    (le₁ : s₁ ⁻¹ᵁ W ≤ act₁ ⁻¹ᵁ W) (t₁ : s₁ ⁻¹ᵁ W ≤ f₁ ⁻¹ᵁ ⊤)
    (H : res le₁ (pullU act₁ W u) = res t₁ (pullU f₁ ⊤ c) * pullU s₁ W u)
    (ha : act₂ ≫ a = b ≫ act₁) (hs : s₂ ≫ a = b ≫ s₁) (hf : f₂ ≫ h = b ≫ f₁)
    (le₂ : s₂ ⁻¹ᵁ W' ≤ act₂ ⁻¹ᵁ W') (t₂ : s₂ ⁻¹ᵁ W' ≤ f₂ ⁻¹ᵁ ⊤) :
    res le₂ (pullU act₂ W' (res hW' (pullU a W u))) =
      res t₂ (pullU f₂ ⊤ c') * pullU s₂ W' (res hW' (pullU a W u)) := by
  refine unit_ext fun y hy => ?_
  have hsy : s₂ y ∈ W' := hy
  have hby : b y ∈ s₁ ⁻¹ᵁ W := by
    have e₁ := congrArg (fun g => g y) hs
    simp only [Scheme.Hom.comp_apply] at e₁
    show s₁ (b y) ∈ W
    rw [← e₁]
    exact hW' hsy
  have hay : act₂ y ∈ W' := le₂ hy
  have o := congrArg (gm b y (s₁ ⁻¹ᵁ W)) H
  rw [map_mul, gm_res b y _ hby, gm_res b y _ hby, gm_pull b act₁ y W (le₁ hby),
    gm_pull b f₁ y ⊤ trivial, gm_pull b s₁ y W hby, ← ha, ← hs, ← hf] at o
  have e3 : gm f₂ y ⊤ c' = gm (f₂ ≫ h) y ⊤ c := by
    subst hc
    refine (gm_res f₂ y (V := ⊤) (U := h ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans ?_
    exact gm_pull f₂ h y ⊤ trivial c
  rw [map_mul, gmRP act₂ y W' _ le₂ hy, gmRP f₂ y ⊤ _ t₂ hy,
    gm_res act₂ y hW' hay, gm_pull act₂ a y W (hW' hay), e3]
  have e2 : gm (𝟙 P₂) y (s₂ ⁻¹ᵁ W') (pullU s₂ W' (res hW' (pullU a W u))) =
      gm (s₂ ≫ a) y W u := by
    rw [gm_pull (𝟙 P₂) s₂ y W' hsy, Category.id_comp, gm_res s₂ y hW' hsy,
      gm_pull s₂ a y W (hW' hsy)]
  rw [e2]
  exact o
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

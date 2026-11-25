-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.equivL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:26.750066+00:00
-- url     : https://prove2.me/submissions/830fbc7c-2c17-43f7-aa6c-74374ec46503

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section GtIso
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
private theorem pullU_comp_lemma {X Y Z : Scheme.{0}} (b : Z ⟶ Y) (a : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    pullU b (a ⁻¹ᵁ W) (pullU a W u) = pullU (b ≫ a) W u := by
  apply Units.ext
  first
    | (simp [pullU]; done)
    | (simp [pullU]; rfl)
    | rfl
private theorem res_pullU_eq_mul_of_eq_of_eq {T Y P : Scheme.{0}} (W : Y.Opens) (u : Γ(Y, W)ˣ) (c : Γ(T, ⊤)ˣ) (F : P ⟶ T)
    (A S A' S' : P ⟶ Y) (hA : A = A') (hS : S = S')
    (le : S ⁻¹ᵁ W ≤ A ⁻¹ᵁ W) (t : S ⁻¹ᵁ W ≤ F ⁻¹ᵁ ⊤)
    (h : res le (pullU A W u) = res t (pullU F ⊤ c) * pullU S W u)
    (le' : S' ⁻¹ᵁ W ≤ A' ⁻¹ᵁ W) (t' : S' ⁻¹ᵁ W ≤ F ⁻¹ᵁ ⊤) :
    res le' (pullU A' W u) = res t' (pullU F ⊤ c) * pullU S' W u := by
  subst hA hS
  exact h
end GtIso
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {T Y Z P₁ P₂ : Scheme.{0}} (act₁ s₁ : P₁ ⟶ Y) (f₁ : P₁ ⟶ T) (b : P₂ ⟶ P₁) (a : Z ⟶ Y) (act₂ s₂ : P₂ ⟶ Z)
    (f₂ : P₂ ⟶ T) (W : Y.Opens) (u : Γ(Y, W)ˣ) (c : Γ(T, ⊤)ˣ) (le₁ : s₁ ⁻¹ᵁ W ≤ act₁ ⁻¹ᵁ W)
    (t₁ : s₁ ⁻¹ᵁ W ≤ f₁ ⁻¹ᵁ ⊤) (h : res le₁ (pullU act₁ W u) = res t₁ (pullU f₁ ⊤ c) * pullU s₁ W u)
    (ha : act₂ ≫ a = b ≫ act₁) (hs : s₂ ≫ a = b ≫ s₁) (hf : f₂ = b ≫ f₁)
    (le₂ : s₂ ⁻¹ᵁ (a ⁻¹ᵁ W) ≤ act₂ ⁻¹ᵁ (a ⁻¹ᵁ W)) (t₂ : s₂ ⁻¹ᵁ (a ⁻¹ᵁ W) ≤ f₂ ⁻¹ᵁ ⊤) :
    res le₂ (pullU act₂ _ (pullU a W u)) = res t₂ (pullU f₂ ⊤ c) * pullU s₂ _ (pullU a W u) := by
  subst hf
  have h' := congrArg (pullU b (s₁ ⁻¹ᵁ W)) h
  rw [map_mul, pullU_res₂, pullU_res₂] at h'
  have key := res_pullU_eq_mul_of_eq_of_eq W u c (b ≫ f₁) (b ≫ act₁) (b ≫ s₁) (act₂ ≫ a) (s₂ ≫ a) ha.symm hs.symm
    (b.preimage_mono le₁) (b.preimage_mono t₁)
    (by
      first
        | exact h'
        | (rw [pullU_comp_lemma, pullU_comp_lemma, pullU_comp_lemma] at h'; exact h')) le₂ t₂
  first
    | exact key
    | (rw [pullU_comp_lemma, pullU_comp_lemma]; exact key)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

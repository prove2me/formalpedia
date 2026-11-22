-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:26.6848+00:00
-- url     : https://prove2.me/submissions/7ae71571-7919-4c89-a254-6d357c140fd9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {G : Over S} {G₁ G₂ : Over S'} [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S' ⟶ S}
    {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f φ₁) (h₂ : IsGrpPullback G₂ G f φ₂) :
    ∃ e : G₁ ≅ G₂, IsMonHom e.hom ∧ e.hom.left ≫ φ₂ = φ₁ := by
  let e : G₁ ≅ G₂ := Over.isoMk (h₁.1.isoIsPullback _ _ h₂.1) (h₁.1.isoIsPullback_hom_snd _ _ h₂.1)
  have he : e.hom.left ≫ φ₂ = φ₁ := h₁.1.isoIsPullback_hom_fst _ _ h₂.1
  have mul : ∀ (T : Over S') (x y : T ⟶ G₁), (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
    intro T x y
    apply Over.OverMorphism.ext
    apply h₂.1.hom_ext
    · rw [Over.comp_left, Category.assoc, he, ← h₁.2 T x y (pushPt h₁.1.w x) (pushPt h₁.1.w y) rfl rfl]
      exact h₂.2 T _ _ _ _ (by show x.left ≫ φ₁ = (x.left ≫ _) ≫ φ₂; rw [Category.assoc, he])
        (by show y.left ≫ φ₁ = (y.left ≫ _) ≫ φ₂; rw [Category.assoc, he])
    · rw [Over.w, Over.w]
  refine ⟨e, ⟨?_, ?_⟩, he⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G₁) ≫ e.hom = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

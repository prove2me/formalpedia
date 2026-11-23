-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:48.096868+00:00
-- url     : https://prove2.me/submissions/648934bd-1ef3-48e1-84d1-3c1277d5a13b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hL : L.IsLB) {K₃ : Type} [Fintype K₃] (φ₁ : K' → (Y' ⟶ X)) (ε₁ : K' → ℤ)
    (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃)) :
    (Out.GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ ε s h φ₃ ε₃ u → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s₁ r z J = sval s (r ≫ h) z J * (val u r z J).val) ∧
    ((∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = sval s (𝟙 Y' ≫ h) y J * (val u (𝟙 Y') y J).val) →
      Out.GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ ε s h φ₃ ε₃ u) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j₁ : K' → L.ι) (j₂ : K → L.ι) (j₃ : K₃ → L.ι)
      (hm : r z ∈ LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃)
      (a₁ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₁ j₁)
      (a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ h ⁻¹ᵁ LB.wchart L φ j₂)
      (a₃ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₃ j₃),
      gs r z _ ((Y'.presheaf.map (homOfLE a₁).op).hom (s₁.f j₁)) = gs r z _ (s₁.f j₁) ∧
      gs r z _ ((Y'.presheaf.map (homOfLE a₂).op).hom ((h.app (LB.wchart L φ j₂)).hom (s.f j₂)) *
        (Y'.presheaf.map (homOfLE a₃).op).hom (u.s j₃).val) =
        gs (r ≫ h) z (LB.wchart L φ j₂) (s.f j₂) * (gm r z (LB.wchart L φ₃ j₃) (u.s j₃)).val :=
    fun Z r z j₁ j₂ j₃ hm a₁ a₂ a₃ => ⟨gs_res r z a₁ hm _, (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z a₂ hm _).trans (gs_pull r h z _ (a₂ hm) _)) ((gs_res r z a₃ hm _).trans (gs_unit r z _ (a₃ hm) _)))⟩
  constructor
  · intro H Z r z J hJ
    rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ⊓
        LB.wchart L φ₃ (fun k => J (r ≫ φ₃ k)) := ⟨⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ k) r⟩, hJ.mem φ₃ r⟩
    have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (fun k => J (r ≫ φ₃ k)) (by
      rintro (a | a | a) (b | b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
    obtain ⟨k₁, k₂⟩ := key Z r z _ _ _ hm _ _ _
    exact k₁.symm.trans ((congrArg (gs r z _) e).trans k₂)
  · intro H j₁ j₂ j₃ hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
      rintro (a | a | a)
      exacts [Set.mem_iInter.1 hy.1.1 a, Set.mem_iInter.1 hy.1.2 a, Set.mem_iInter.1 hy.2 a])
    have := H y J hJ
    rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
      sval_of s _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr (.inl k))),
      val_of u _ y J j₃ (fun k => by rw [Category.id_comp]; exact e (.inr (.inr k)))] at this
    obtain ⟨k₁, k₂⟩ := key _ (𝟙 Y') y j₁ j₂ j₃ hy _ _ _
    exact k₁.trans (this.trans k₂.symm)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

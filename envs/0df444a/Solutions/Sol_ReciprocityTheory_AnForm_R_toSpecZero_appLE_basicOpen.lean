-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:27.597186+00:00
-- url     : https://prove2.me/submissions/4526473a-8b19-4589-b740-fd0f0c61bb2d

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable [Nonempty K]
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f := by
  have hg : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι := by
    show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _
    rw [Iso.hom_inv_id_assoc]
  have hB : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero 𝒜 f f_deg hm, ← Category.assoc, hg]
  have h1 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop := by
    rw [Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.appLE_map]
  have h2 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f) ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [h1, ← Scheme.Hom.comp_appTop, hB, Scheme.Hom.comp_appTop]
    have hA : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 f) =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom ≫
          Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv :=
      Proj.basicOpenToSpec_app_top 𝒜 f
    rw [hA]
    rw [← Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  have h3 := (cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).1 h2
  rw [h3, Iso.inv_hom_id_assoc]
end ReciprocityTheory.AnForm.R

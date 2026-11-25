-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.sec_algebraMap_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:19.293027+00:00
-- url     : https://prove2.me/submissions/c915912a-3968-4e2f-a11d-bad6ee9afef7

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Theorems.Thm_ReciprocityTheory_AnForm_R_isAffineOpen_of_iso
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {X W : Scheme.{0}} (π : W ⟶ X) (U : X.affineOpens) (V : W.Opens)
    (hV : V ≤ π ⁻¹ᵁ U.1) (A : Type) [CommRing A] [Algebra Γ(X, U.1) A]
    (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) ≫ U.2.fromSpec = V.ι ≫ π)
    (r : Γ(X, U.1)) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r))) = π.appLE _ V hV r := by
  have hVa := isAffineOpen_of_iso V e
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hVa hV
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  have h3 : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) =
      hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV) := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, he, Category.assoc, h1, ← Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec]
  have n1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
      ((Scheme.ΓSpecIso _).inv r) = (Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have n2 : (Spec.map (π.appLE _ V hV)).appTop ((Scheme.ΓSpecIso _).inv r) =
      (Scheme.ΓSpecIso _).inv (π.appLE _ V hV r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have n3 : ∀ x : Γ(W, V), hVa.isoSpec.hom.appTop ((Scheme.ΓSpecIso _).inv x) = V.topIso.inv x := by
    intro x
    rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, Iso.inv_hom_id, CommRingCat.id_apply]
  calc V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r)))
      = V.topIso.hom ((e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n1]
    _ = V.topIso.hom ((hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV)).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by rw [h3]; rfl
    _ = π.appLE _ V hV r := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [n2, n3]
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
end ReciprocityTheory.AnForm.R

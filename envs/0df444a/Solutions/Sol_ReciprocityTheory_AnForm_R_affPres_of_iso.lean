-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.affPres_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:34.439562+00:00
-- url     : https://prove2.me/submissions/e95b27d8-635e-43f3-9e77-aae5eb2d5305

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts

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
theorem _root_.solution {W : Scheme.{0}} (s : W ⟶ Spec (.of ℂ)) (V : W.Opens) (A : Type) [CommRing A]
    [Algebra ℂ A] (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = V.ι ≫ s) (n : ℕ) (y : Fin n → A)
    (hy : Algebra.adjoin ℂ (Set.range y) = ⊤) :
    ∃ (I : Ideal (MvPolynomial (Fin n) ℂ)) (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I))) = V.ι ≫ s),
      ∀ l : Fin n, (AffPres.mk V n I iso hiso : AffPres s).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (y l))) := by
  have hs : Function.Surjective (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) := by
    rw [← AlgHom.range_eq_top, aeval_range, hy]
  let ψ := Ideal.quotientKerAlgEquivOfSurjective hs
  let iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A))) :=
    e ≪≫ asIso (Spec.map (RingEquiv.toCommRingCatIso ψ.toRingEquiv).hom)
  have hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸
      RingHom.ker (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)))) = V.ι ≫ s := by
    rw [← he]
    simp only [iso, Iso.trans_hom, Category.assoc]
    congr 1
    simp only [asIso_hom]
    rw [← Spec.map_comp]
    congr 2
    ext c
    simp [ψ]
  refine ⟨_, iso, hiso, fun l => ?_⟩
  have key : (Spec.map (RingEquiv.toCommRingCatIso ψ.toRingEquiv).hom).appTop
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (X l))) = (Scheme.ΓSpecIso (.of A)).inv (y l) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    show ψ (Ideal.Quotient.mk _ (X l)) = y l
    simp [ψ, Ideal.quotientKerAlgEquivOfSurjective_mk]
  simp only [AffPres.secHom, RingHom.comp_apply, iso, Iso.trans_hom, asIso_hom, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact congrArg _ (congrArg _ key)
end ReciprocityTheory.AnForm.R

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.StalkLocB.secH_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:21.151897+00:00
-- url     : https://prove2.me/submissions/9ec5713f-2397-4fd0-985a-c14f3e43fa4f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
variable {K iso}
namespace ReciprocityTheory.AnForm.R.StalkLocB
theorem _root_.solution (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (c : ℂ) :
    secH V K iso (C c) = W.presheaf.map (homOfLE le_top : V ⟶ ⊤).op
      (s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) := by
  have h := congrArg (fun g => CommRingCat.Hom.hom g ((Scheme.ΓSpecIso (.of ℂ)).inv c))
    (congrArg Scheme.Hom.appTop hover)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  have hnat := congrArg (fun g => CommRingCat.Hom.hom g c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  rw [← hnat] at h
  show V.topIso.hom (iso.hom.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv
    (Ideal.Quotient.mk K (C c)))) = _
  have hc : Ideal.Quotient.mk K (C c) = algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K) c := rfl
  rw [hc]
  erw [h]
  rw [Scheme.Opens.topIso_hom, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  erw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
end ReciprocityTheory.AnForm.R.StalkLocB

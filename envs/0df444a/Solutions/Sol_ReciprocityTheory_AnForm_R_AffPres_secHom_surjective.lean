-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.secHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:04:03.068499+00:00
-- url     : https://prove2.me/submissions/eaa84d93-bf9b-484e-a182-a52abff565aa

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
namespace ReciprocityTheory.AnForm.R.AffPres
theorem _root_.solution (P : AffPres sW) : Function.Surjective P.secHom := by
  intro a
  have h1 : Function.Surjective P.V.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2
  have h2 : Function.Surjective (P.iso.hom.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  obtain ⟨a1, rfl⟩ := h1 a
  obtain ⟨a2, rfl⟩ := h2 a1
  obtain ⟨a3, rfl⟩ := h3 a2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a3
  exact ⟨f, rfl⟩
end ReciprocityTheory.AnForm.R.AffPres

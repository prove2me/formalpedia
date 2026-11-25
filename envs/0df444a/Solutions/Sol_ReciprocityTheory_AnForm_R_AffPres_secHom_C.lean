-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.secHom_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:26.436618+00:00
-- url     : https://prove2.me/submissions/53c957a7-190f-484b-95b5-e7e7c8031d2d

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
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.AnForm.R.AffPres
theorem _root_.solution (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top := by
    rw [← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]
    rfl
  have e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom) c := rfl
  rw [e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]
  rfl
end ReciprocityTheory.AnForm.R.AffPres

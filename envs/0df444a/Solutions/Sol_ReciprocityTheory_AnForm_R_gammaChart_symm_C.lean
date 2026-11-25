-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.gammaChart_symm_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:16.250604+00:00
-- url     : https://prove2.me/submissions/c919c2a6-0cc7-4511-bf73-728ce07eb3ac

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Theorems.Thm_ReciprocityTheory_AnForm_R_toSpecZero_appLE_basicOpen


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
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (c : ℂ) :
    (gammaChart hP p).symm (Ideal.Quotient.mk _ (C c)) = constSec (toSpecC hP) (chartOpen hP p).1 c := by
  letI := segreGraded hP
  have hk := toSpecZero_appLE_basicOpen (segreGrading P) (segreW_mem P p) one_pos
  have hC : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (toSpecC hP).appLE ⊤ (chartOpen hP p).1 le_top =
      CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)) ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (segreGrading P)
          (Submonoid.powers (segreW P p))) ≫ Proj.awayToSection (segreGrading P) (segreW P p) := by
    have h3 := Scheme.Hom.comp_appLE (Proj.toSpecZero (segreGrading P))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))) ⊤
      (Proj.basicOpen (segreGrading P) (segreW P p)) le_top
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Scheme.Hom.appLE (Proj.toSpecZero (segreGrading P) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))) ⊤
      (Proj.basicOpen (segreGrading P) (segreW P p)) le_top = _
    have h4 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))
    rw [h3, ← Category.assoc]
    refine (congrArg (· ≫ _) h4.symm).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)) ≫ ·) hk)
  have hl : (gammaChart hP p).symm (Ideal.Quotient.mk _ (C c)) =
      (Proj.awayToSection (segreGrading P) (segreW P p)).hom
        (HomogeneousLocalization.fromZeroRingHom (segreGrading P) (Submonoid.powers (segreW P p))
          (algebraMap ℂ (segreGrading P 0) c)) := by
    show (Proj.awayToSection (segreGrading P) (segreW P p)).hom (polyToAway hP p (C c)) = _
    simp only [polyToAway, coe_eval₂Hom, eval₂_C, RingHom.comp_apply]
    rfl
  rw [hl]
  show _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (toSpecC hP).appLE ⊤ (chartOpen hP p).1 le_top).hom c
  rw [hC]
  rfl
end ReciprocityTheory.AnForm.R

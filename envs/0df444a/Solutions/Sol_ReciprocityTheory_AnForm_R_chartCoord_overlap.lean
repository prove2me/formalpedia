-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.chartCoord_overlap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:55.270437+00:00
-- url     : https://prove2.me/submissions/96de763e-532f-486d-83e2-a588da21349d

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreW_exchange


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
    (p p' : (k : K) → ι k) (q : Σ k, ι k) :
    (projX P hP).presheaf.map (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
        (chartCoord hP p q) *
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
        (chartCoord hP p' ⟨q.1, p q.1⟩) =
    (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
        (chartCoord hP p' q) := by
  letI := segreGraded hP
  classical
  have hcc : ∀ p₀ q₀, chartCoord hP p₀ q₀ =
      (Proj.awayToSection (segreGrading P) (segreW P p₀)).hom (awayCoord hP p₀ q₀) := by
    intro p₀ q₀
    show (Proj.awayToSection (segreGrading P) (segreW P p₀)).hom (polyToAway hP p₀ (X q₀)) = _
    simp only [polyToAway, coe_eval₂Hom, eval₂_X]
  have key : ∀ (V : (projX P hP).Opens) (h1 : V ≤ (chartOpen hP p).1) (h2 : V ≤ (chartOpen hP p').1),
      V = Proj.basicOpen (segreGrading P) (segreW P p * segreW P p') →
      (projX P hP).presheaf.map (homOfLE h1).op (chartCoord hP p q) *
        (projX P hP).presheaf.map (homOfLE h2).op (chartCoord hP p' ⟨q.1, p q.1⟩) =
      (projX P hP).presheaf.map (homOfLE h2).op (chartCoord hP p' q) := by
    rintro V h1 h2 rfl
    have e1 : ∀ a, (projX P hP).presheaf.map (homOfLE h1).op
        ((Proj.awayToSection (segreGrading P) (segreW P p)).hom a) =
        (Proj.awayToSection (segreGrading P) (segreW P p * segreW P p')).hom
          (HomogeneousLocalization.awayMap (segreGrading P) (segreW_mem P p') rfl a) := fun a =>
      (congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (𝒜 := segreGrading P) (f := segreW P p)
        (segreW_mem P p') (hx := rfl))).symm
    have e2 : ∀ a, (projX P hP).presheaf.map (homOfLE h2).op
        ((Proj.awayToSection (segreGrading P) (segreW P p')).hom a) =
        (Proj.awayToSection (segreGrading P) (segreW P p * segreW P p')).hom
          (HomogeneousLocalization.awayMap (segreGrading P) (segreW_mem P p) (mul_comm _ _) a) := fun a =>
      (congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (𝒜 := segreGrading P) (f := segreW P p')
        (segreW_mem P p) (hx := mul_comm _ _))).symm
    rw [hcc, hcc, hcc, e1, e2, e2]
    refine (map_mul (Proj.awayToSection (segreGrading P) (segreW P p * segreW P p')).hom _ _).symm.trans ?_
    congr 1
    apply HomogeneousLocalization.val_injective
    have E := segreW_exchange P p p' q
    simp only [HomogeneousLocalization.val_mul, awayCoord, HomogeneousLocalization.awayMap_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [chartUpd, Submonoid.coe_mul, OneMemClass.coe_one, pow_one, one_mul]
    linear_combination (segreW P p * segreW P p' * segreW P p' * segreW P p) * E
  exact key _ inf_le_left inf_le_right (Proj.basicOpen_mul _ _ _).symm
end ReciprocityTheory.AnForm.R

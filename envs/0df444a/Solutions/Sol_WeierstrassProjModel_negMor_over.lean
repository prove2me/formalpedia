-- Prove2me | solution 1 for WeierstrassProjModel.negMor_over
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fc69438a-7efc-5f99-9f8f-62236ecf1f60

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_negMor_over

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

private theorem sol_Away_map_fromZeroRingHom {A : Type u} [CommRing A] {σ : Type u}
    [SetLike σ A] [AddSubgroupClass σ A] {𝒢 : ℕ → σ} [GradedRing 𝒢]
    (g : 𝒢 →+*ᵍ 𝒢) (s : A) :
    (HomogeneousLocalization.Away.map g s).comp (fromZeroRingHom 𝒢 (.powers s))
      = (fromZeroRingHom 𝒢 (.powers (g s))).comp g.gradedZeroRingHom := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply]
  ext
  show (HomogeneousLocalization.map g _
      (HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩)).val
    = (HomogeneousLocalization.mk
        ⟨0, g.gradedZeroRingHom a, 1, one_mem _⟩
          : HomogeneousLocalization 𝒢 (.powers (g s))).val
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk, GradedRingHom.gradedZeroRingHom_apply_coe]
  congr 1
  exact Subtype.ext (by simp)

set_option backward.isDefEq.respectTransparency false in

private theorem sol_Proj_map_toSpecZero {A : Type u} [CommRing A] {σ : Type u}
    [SetLike σ A] [AddSubgroupClass σ A] {𝒢 : ℕ → σ} [GradedRing 𝒢] (g : 𝒢 →+*ᵍ 𝒢)
    (hg : HomogeneousIdeal.irrelevant 𝒢 ≤ (HomogeneousIdeal.irrelevant 𝒢).map g) :
    Proj.map g hg ≫ Proj.toSpecZero 𝒢
      = Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom g.gradedZeroRingHom) := by
  refine (Proj.mapAffineOpenCover g hg).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    Proj.mapAffineOpenCover_f, Proj.awayι_comp_map_assoc g hg s.1.2 _ s.2.2,
    Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    sol_Away_map_fromZeroRingHom]

private theorem sol_negGradedHom_zero_comp_algebraMap {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) :
    (kw_lrAddNegDiag_negGradedHom W).gradedZeroRingHom.comp
        (algebraMap R (projModelGradingCR W.toProjective 0))
      = algebraMap R (projModelGradingCR W.toProjective 0) := by
  refine RingHom.ext fun r => Subtype.ext ?_
  show kw_lrAddNegDiag_negGradedHom W
      ↑(algebraMap R (projModelGradingCR W.toProjective 0) r)
    = ↑(algebraMap R (projModelGradingCR W.toProjective 0) r)
  have halg : (↑(algebraMap R (projModelGradingCR W.toProjective 0) r)
      : ProjModelRingCR W.toProjective)
    = algebraMap R (ProjModelRingCR W.toProjective) r := rfl
  rw [halg]
  show kw_lrAddNegDiag_negQuotHom W (algebraMap R (ProjModelRingCR W.toProjective) r)
    = algebraMap R (ProjModelRingCR W.toProjective) r
  show Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
      (kw_lrAddNegDiag_negSubst W (C r))
    = Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (C r)
  rw [show kw_lrAddNegDiag_negSubst W (C r) = C r
    from (kw_lrAddNegDiag_negSubst W).commutes r]

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective
      = projModelStrCR W.toProjective := by
  show Proj.map (kw_lrAddNegDiag_negGradedHom W)
        (kw_lrAddNegDiag_negGradedHom_irrelevant_le W)
      ≫ (Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (projModelGradingCR W.toProjective 0))))
    = Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (projModelGradingCR W.toProjective 0)))
  rw [← Category.assoc,
    sol_Proj_map_toSpecZero (kw_lrAddNegDiag_negGradedHom W)
      (kw_lrAddNegDiag_negGradedHom_irrelevant_le W),
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    sol_negGradedHom_zero_comp_algebraMap W]

end S_WeierstrassProjModel_negMor_over
end P2MW
export P2MW.S_WeierstrassProjModel_negMor_over (solution)

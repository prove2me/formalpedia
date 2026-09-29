-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_map_mul_of_delta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3ff25ad6-79f3-5706-86c7-ef8e57c9d5a1

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_a2_liftAddMor_factor
import Theorems.Thm_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_map_mul_of_delta_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option Elab.async false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrChart_gen kw_lrSixU KwLRSixUCoverage kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap KwLRPerChartCompat kw_lrPerChart_toE projModelAffineOpenCoverCR KwLROuterCompat kw_lrAddMorphism kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_liftAddMor_factor kw_a2_sixU_class_eq_addMap_of_delta_ne_zero"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_a2_map_mul_of_delta_ne_zero.WeierstrassProjModel NeronModelInfra"

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

section MapMulRaw

open scoped TensorProduct WeierstrassCurve.Projective

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W

variable (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
  (houter : KwLROuterCompat W) (hΔ : algebraMap R F W.Δ ≠ 0)

theorem kw_lrSixU_cover_openCover_f (i j : Fin 3)
    (h : Ideal.span (Set.range (kw_lrSixU W i j)) = ⊤) (l : Fin 3 ⊕ Fin 3) :
    (kw_lrSixU_cover W i j h).openCover.f l = kw_lrSixU_locMap W i j l := rfl

include hcov in

theorem kw_lrApt_exists_sixU_ne_zero (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    ∃ l, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l) ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hker : Set.range (kw_lrSixU W i j)
      ⊆ RingHom.ker (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom := by
    rintro _ ⟨l, rfl⟩; exact hall l
  have htop : (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j)))
      ≤ RingHom.ker (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom :=
    hcov i j ▸ Ideal.span_le.mpr hker
  have h1 : (Algebra.TensorProduct.productMap ψᵢ ψⱼ) 1 = 0 := htop Submodule.mem_top
  rw [map_one] at h1
  exact one_ne_zero h1

theorem kw_lrApt_perChart_factor (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
        ≫ kw_lrPerChart_toE W hcov hcompat i j
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l := by

  have hfact : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ (kw_lrSixU_cover W i j (hcov i j)).openCover.f l := by
    rw [kw_lrSixU_cover_openCover_f, kw_lrSixU_locMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]

  have hgl : (kw_lrSixU_cover W i j (hcov i j)).openCover.f l
        ≫ kw_lrPerChart_toE W hcov hcompat i j
      = kw_lrSixU_toE W i j l :=
    (kw_lrSixU_cover W i j (hcov i j)).openCover.ι_glueMorphisms
      (kw_lrSixU_toE W i j) (hcompat i j) l
  exact (congrArg (· ≫ kw_lrPerChart_toE W hcov hcompat i j) hfact).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hgl))

end MapMulRaw

attribute [local instance] MvPolynomial.gradedAlgebra in
attribute [local instance] kw_pbac_awayAlgebra in
set_option maxHeartbeats 12800000 in
theorem _root_.P2MW.S_WeierstrassProjModel_kw_a2_map_mul_of_delta_ne_zero.solution {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (hΔ : algebraMap R F W.Δ ≠ 0)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
    (houter : KwLROuterCompat W) (i j : Fin 3)
    (ψᵢ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (ψⱼ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X j : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (k : Fin 3) (ψₖ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (x y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (hfacx : x.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hfacy : y.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f j)
    (hfacsum : pullback.lift x.1 y.1 (x.2.trans y.2.symm)
        ≫ kw_lrAddMorphism W hcov hcompat houter
      = Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = (kw_lrApt_WF W F).addMap ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by
  obtain ⟨l, hl⟩ := kw_lrApt_exists_sixU_ne_zero W F hcov i j ψᵢ ψⱼ
  have hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)) :=
    isUnit_iff_ne_zero.mpr hl
  have h1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
        ≫ kw_lrPerChart_toE W hcov hcompat i j
      = Spec.map (CommRingCat.ofHom ψₖ.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k :=
    (kw_a2_liftAddMor_factor W F hcov hcompat houter i j ψᵢ ψⱼ x y hfacx hfacy).symm.trans hfacsum
  exact kw_a2_sixU_class_eq_addMap_of_delta_ne_zero W F hΔ i j ψᵢ ψⱼ l hu k ψₖ
    ((kw_lrApt_perChart_factor W F hcov hcompat i j ψᵢ ψⱼ l hu).symm.trans h1)

end WeierstrassProjModel

end
end S_WeierstrassProjModel_kw_a2_map_mul_of_delta_ne_zero
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_map_mul_of_delta_ne_zero (solution)

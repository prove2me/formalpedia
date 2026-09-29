-- Prove2me | solution 1 for WeierstrassProjModel.pin_addMorphism_negMor_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e349803a-2af5-5992-9cb1-fce807812fdf

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_kw_a2_map_one
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Theorems.Thm_WeierstrassProjModel_negMor_over
import Theorems.Thm_WeierstrassProjModel_negMor_chartFactor
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Theorems.Thm_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne
import Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_not_two_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option Elab.async false

section MEGA_DensityKit_lean

noncomputable section

p2m_open "AlgebraicGeometry P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.AlgebraicGeometry CategoryTheory CategoryTheory.Limits"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion"
namespace Density
p2m_open "WeierstrassProjModel"

universe u

section Integral

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {X : Scheme.{u}}

theorem isIntegral_of_smooth_of_geometricallyIntegral (q : X ⟶ Spec (CommRingCat.of R))
    [Smooth q] [GeometricallyIntegral q] : IsIntegral X :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian q

end Integral

section GenericPoint

variable (X : Scheme.{u}) [IsIntegral X]

abbrev genericInclusion : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

theorem isDominant_genericInclusion : IsDominant (genericInclusion X) := by
  rw [isDominant_iff, DenseRange, Scheme.range_fromSpecStalk]
  refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl _)) ?_
  exact dense_iff_closure_eq.mpr (genericPoint_spec X)

scoped instance isSchemeTheoreticallyDominant_genericInclusion :
    IsSchemeTheoreticallyDominant (genericInclusion X) := by
  haveI := isDominant_genericInclusion X
  exact IsSchemeTheoreticallyDominant.of_isDominant (genericInclusion X)

variable {X} {R : Type u} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R))

abbrev functionFieldAlgebra : Algebra R X.functionField :=
  (Spec.preimage (genericInclusion X ≫ q)).hom.toAlgebra

theorem genericInclusion_comp :
    letI := functionFieldAlgebra q
    genericInclusion X ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) := by
  letI := functionFieldAlgebra q
  show genericInclusion X ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

end GenericPoint

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end MEGA_DensityKit_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

section MEGA_DensityIdentities_lean

noncomputable section

p2m_open "AlgebraicGeometry P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion"
namespace Density
p2m_open "WeierstrassProjModel"

universe u v

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R))

section Points

variable (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)

abbrev addPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver t q) :
    SchemeHomOver t q :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m,
    by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2]⟩

variable (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q)

abbrev onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t q :=
  ⟨t ≫ o.1, by rw [Category.assoc, o.2, Category.comp_id]⟩

variable (i : X ⟶ X) (hi : i ≫ q = q)

abbrev invPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t q) :
    SchemeHomOver t q :=
  ⟨x.1 ≫ i, by rw [Category.assoc, hi, x.2]⟩

include hi in

theorem inv_id_cond : i ≫ q = 𝟙 X ≫ q := by
  rw [hi, Category.id_comp]

end Points
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

section Identities

variable {q} [IsSeparated q] (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  {P : Type v} [AddCommGroup P]

theorem inv_mul_eq_unit' [IsIntegral X] [Algebra R X.functionField]
    (halg : genericInclusion X ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)))
    (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q) (i : X ⟶ X) (hi : i ≫ q = q)
    (e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) q → P)
    (he : Function.Injective e)
    (hmul : ∀ x y, e x ≠ e y → e (addPt q m hm x y) = e x + e y)
    (hone : e (onePt q o _) = 0)
    (hinv : ∀ x, e (invPt q i hi x) = -e x)
    (hgen2 : (2 : ℤ) • e ⟨genericInclusion X, halg⟩ ≠ 0) :
    pullback.lift i (𝟙 X) (inv_id_cond q i hi) ≫ m = q ≫ o.1 := by
  let xj : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) q :=
    ⟨genericInclusion X, halg⟩
  have hne : e (invPt q i hi xj) ≠ e xj := by
    rw [hinv]; intro h
    refine hgen2 ?_
    rw [two_zsmul]
    nth_rw 1 [← h]
    exact neg_add_cancel (e xj)
  have key : addPt q m hm (invPt q i hi xj) xj = onePt q o _ :=
    he (by rw [hmul _ _ hne, hinv, neg_add_cancel, hone])
  have hfac : genericInclusion X ≫ pullback.lift i (𝟙 X) (inv_id_cond q i hi)
      = pullback.lift (invPt q i hi xj).1 xj.1 ((invPt q i hi xj).2.trans xj.2.symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, xj]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, xj]
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated q ?_ (genericInclusion X) ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, hi, Category.assoc, o.2, Category.comp_id]
  · rw [← Category.assoc, hfac]
    exact (congrArg Subtype.val key).trans
      ((congrArg (· ≫ o.1) halg.symm).trans (Category.assoc _ _ _))

end Identities
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end MEGA_DensityIdentities_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

section MEGA_EvalBridge

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F]

noncomputable def kw_ev_e (hΔF : algebraMap R F W.Δ ≠ 0) :
    SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective) → (kw_lrApt_WF W F).Point :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose

theorem kw_ev_injective (hΔF : algebraMap R F W.Δ ≠ 0) : Function.Injective (kw_ev_e W F hΔF) :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose_spec.1

theorem kw_ev_point (hΔF : algebraMap R F W.Δ ≠ 0)
    (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    (kw_ev_e W F hΔF x).point
      = (⟦kw_lrApt_chartEval W F i ψ⟧ : WeierstrassCurve.Projective.PointClass F) :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose_spec.2 x i ψ hfac

theorem kw_ev_factor (hΔF : algebraMap R F W.Δ ≠ 0)
    (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) :
    ∃ (i : Fin 3) (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F),
      x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).1 x

theorem kw_ev_rechart (hΔF : algebraMap R F W.Δ ≠ 0)
    (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (k : Fin 3) (hk : kw_lrApt_chartEval W F i ψ k ≠ 0) :
    ∃ ψ' : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F,
      x.1 = Spec.map (CommRingCat.ofHom ψ'.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.1 x i ψ hfac k hk

theorem kw_ev_map_one (hΔF : algebraMap R F W.Δ ≠ 0)
    (h : (kw_lrAptb_tF (R := R) F ≫ (kwZeroSect R W).1) ≫ projModelStrCR W.toProjective
        = kw_lrAptb_tF (R := R) F) :
    kw_ev_e W F hΔF ⟨kw_lrAptb_tF (R := R) F ≫ (kwZeroSect R W).1, h⟩ = 0 := by
  obtain ⟨k, ψₖ, hs⟩ := kw_ev_factor W F hΔF
    ⟨kw_lrAptb_tF (R := R) F ≫ (kwZeroSect R W).1, h⟩
  apply WeierstrassCurve.Projective.Point.ext
  rw [WeierstrassCurve.Projective.Point.zero_point, kw_ev_point W F hΔF _ k ψₖ hs]
  exact WeierstrassProjModel.kw_a2_map_one W F k ψₖ hs

theorem kw_ev_pin_map_mul_of_ne (hΔF : algebraMap R F W.Δ ≠ 0)
    (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
    (hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m
      = kw_lrSixU_toE W i j l)
    (x y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (h : (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ≫ projModelStrCR W.toProjective
        = kw_lrAptb_tF (R := R) F)
    (hne : kw_ev_e W F hΔF x ≠ kw_ev_e W F hΔF y) :
    kw_ev_e W F hΔF ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m, h⟩
      = kw_ev_e W F hΔF x + kw_ev_e W F hΔF y := by
  obtain ⟨i, ψᵢ, hx⟩ := kw_ev_factor W F hΔF x
  obtain ⟨j, ψⱼ, hy⟩ := kw_ev_factor W F hΔF y
  obtain ⟨k, ψₖ, hs⟩ := kw_ev_factor W F hΔF
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m, h⟩
  apply WeierstrassCurve.Projective.Point.ext
  rw [WeierstrassCurve.Projective.Point.add_point, kw_ev_point W F hΔF _ k ψₖ hs,
    kw_ev_point W F hΔF x i ψᵢ hx, kw_ev_point W F hΔF y j ψⱼ hy]
  refine kw_a2_pin_map_mul_of_ne W F hΔF m hmpin i j ψᵢ ψⱼ k ψₖ x y hx hy hs ?_
  intro heq
  exact hne (WeierstrassCurve.Projective.Point.ext
    ((kw_ev_point W F hΔF x i ψᵢ hx).trans
      (heq.trans (kw_ev_point W F hΔF y j ψⱼ hy).symm)))

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end MEGA_EvalBridge
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

namespace WeierstrassProjModel p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion" end WeierstrassProjModel
p2m_open_scoped "WeierstrassProjModel" in
open CategoryTheory _root_.AlgebraicGeometry _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel in
theorem WeierstrassProjModel.kw_lrAddNegDiag_negMor_over {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective = projModelStrCR W.toProjective :=
  WeierstrassProjModel.negMor_over W

section MEGA_MapNegRaw_lean

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicGeometry P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra"

namespace WeierstrassProjModel p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion" namespace Density end WeierstrassProjModel.Density
p2m_open_scoped "WeierstrassProjModel" in
theorem WeierstrassProjModel.Density.apply_involutive_eq_neg {α : Type*} {P : Type*} [AddGroup P]
    (σ : α → α) (hσ : ∀ a, σ (σ a) = a) (f : α → P)
    (h : ∀ a, f a ≠ 0 → f (σ a) = -f a) (a : α) : f (σ a) = -f a := by
  by_cases ha : f a = 0
  · by_contra hne
    have h1 : f (σ a) ≠ 0 := fun h0 => hne (by rw [h0, ha, neg_zero])
    have h2 := h (σ a) h1
    rw [hσ, ha, zero_eq_neg] at h2
    exact h1 h2
  · exact h a ha

section ProjMapCongr

universe u

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_preimage GeometricallyIntegral GeometricallyIntegral.isIntegral_of_isLocallyNoetherian Scheme.range_fromSpecStalk Spec IsIntegral Spec.map Scheme Smooth Proj.map_id Proj IsSchemeTheoreticallyDominant IsSeparated Spec.preimage IsDominant isDominant_iff IsSchemeTheoreticallyDominant.of_isDominant Proj.map Proj.map_comp" namespace Proj p2m_export "AlgebraicGeometry.Proj" "map_id ext map map_comp" end AlgebraicGeometry.Proj
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Proj" in
theorem AlgebraicGeometry.Proj.map_congr' {f g : 𝒜 →+*ᵍ ℬ} (hfg : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf = Proj.map g (hfg ▸ hf) := by
  subst hfg
  rfl

end ProjMapCongr
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W
set_option quotPrecheck false in
local notation "negMor" => kw_lrAddNegDiag_negMor W

theorem kw_lrMnr_negMor_comp_negMor : negMor ≫ negMor = 𝟙 E := by
  have hcomp : (negGradedHom).comp negGradedHom
      = GradedRingHom.id (projModelGradingCR W.toProjective) :=
    GradedRingHom.ext fun x =>
      RingHom.congr_fun (kw_lrAddNegDiag_negGradedHom_comp_self W) x
  calc negMor ≫ negMor
      = Proj.map ((negGradedHom).comp negGradedHom)
          (HomogeneousIdeal.irrelevant_le_map_comp
            (kw_lrAddNegDiag_negGradedHom_irrelevant_le W)
            (kw_lrAddNegDiag_negGradedHom_irrelevant_le W)) :=
        (Proj.map_comp _ _ _ _).symm
    _ = Proj.map (GradedRingHom.id (projModelGradingCR W.toProjective)) _ :=
        Proj.map_congr' hcomp _
    _ = 𝟙 E := Proj.map_id

abbrev kw_lrMnr_negPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t π) : SchemeHomOver t π :=
  ⟨x.1 ≫ negMor, by rw [Category.assoc, kw_lrAddNegDiag_negMor_over W, x.2]⟩

theorem kw_lrMnr_negPt_negPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t π) : kw_lrMnr_negPt W (kw_lrMnr_negPt W x) = x :=
  Subtype.ext (by
    show (x.1 ≫ negMor) ≫ negMor = x.1
    rw [Category.assoc, kw_lrMnr_negMor_comp_negMor, Category.comp_id])

section Field

variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F

end Field
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end MEGA_MapNegRaw_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

section MEGA_NegBridge

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kw_lrAddNegDiag_negGradedHom kw_lrAddNegDiag_negGradedHom_comp_self kw_lrAddNegDiag_negGradedHom_irrelevant_le kw_lrAddNegDiag_negMor kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange negMor_over negMor_chartFactor kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_not_two_torsion"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F]

theorem kw_ev_eq_zero_of_Z (hΔF : algebraMap R F W.Δ ≠ 0) (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hz : kw_lrApt_chartEval W F i ψ 2 = 0) :
    kw_ev_e W F hΔF x = 0 := by
  apply WeierstrassCurve.Projective.Point.ext
  have hns : (kw_lrApt_WF W F).Nonsingular (kw_lrApt_chartEval W F i ψ) := by
    have h := (kw_ev_e W F hΔF x).nonsingular
    rw [kw_ev_point W F hΔF x i ψ hfac] at h
    exact h
  rw [kw_ev_point W F hΔF x i ψ hfac, WeierstrassCurve.Projective.Point.zero_point]
  exact Quotient.sound (WeierstrassCurve.Projective.equiv_of_Z_eq_zero hns
    WeierstrassCurve.Projective.nonsingular_zero hz rfl)

theorem kw_ev_map_neg (hΔF : algebraMap R F W.Δ ≠ 0) (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (h : (x.1 ≫ kw_lrAddNegDiag_negMor W) ≫ projModelStrCR W.toProjective = kw_lrAptb_tF (R := R) F) :
    kw_ev_e W F hΔF ⟨x.1 ≫ kw_lrAddNegDiag_negMor W, h⟩ = -kw_ev_e W F hΔF x := by
  obtain ⟨ν, hν1, hν2⟩ := WeierstrassProjModel.negMor_chartFactor W F
  have key : ∀ y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective), kw_ev_e W F hΔF y ≠ 0 →
      kw_ev_e W F hΔF (kw_lrMnr_negPt W y) = -kw_ev_e W F hΔF y := by
    intro y hne
    obtain ⟨i, ψ, hfac⟩ := kw_ev_factor W F hΔF y
    have hz : kw_lrApt_chartEval W F i ψ 2 ≠ 0 :=
      fun hz => hne (kw_ev_eq_zero_of_Z W F hΔF y i ψ hfac hz)
    obtain ⟨ψ₂, hfac₂⟩ := kw_ev_rechart W F hΔF y i ψ hfac 2 hz
    have hfacn : (kw_lrMnr_negPt W y).1
        = Spec.map (CommRingCat.ofHom (ψ₂.comp ν).toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) :=
      hν1 ψ₂ y hfac₂
    apply WeierstrassCurve.Projective.Point.ext
    rw [WeierstrassCurve.Projective.Point.neg_point, kw_ev_point W F hΔF _ 2 (ψ₂.comp ν) hfacn,
      kw_ev_point W F hΔF y 2 ψ₂ hfac₂, hν2 ψ₂]
    rfl
  exact Density.apply_involutive_eq_neg (kw_lrMnr_negPt W) (kw_lrMnr_negPt_negPt W)
    (kw_ev_e W F hΔF) key x

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end MEGA_NegBridge
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel"
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
    (hm_over : m ≫ projModelStrCR W.toProjective
        = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective)
    (hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m
      = kw_lrSixU_toE W i j l)
    (hnego : kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective
        = projModelStrCR W.toProjective) :
    pullback.lift (kw_lrAddNegDiag_negMor W) (𝟙 (projModelCR W.toProjective))
        (by rw [hnego, Category.id_comp])
      ≫ m = projModelStrCR W.toProjective ≫ (kwZeroSect R W).1 := by
  haveI : Smooth (projModelStrCR W.toProjective) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsIntegral (projModelCR W.toProjective) :=
    Density.isIntegral_of_smooth_of_geometricallyIntegral (projModelStrCR W.toProjective)
  letI : Algebra R (projModelCR W.toProjective).functionField :=
    Density.functionFieldAlgebra (projModelStrCR W.toProjective)
  have hΔF : algebraMap R (projModelCR W.toProjective).functionField W.Δ ≠ 0 :=
    (W.isUnit_Δ.map _).ne_zero

  have hgen2 : (2 : ℤ) • kw_ev_e W _ hΔF
      ⟨Density.genericInclusion (projModelCR W.toProjective),
        Density.genericInclusion_comp (projModelStrCR W.toProjective)⟩ ≠ 0 :=
    kw_ev_genericPoint_not_two_torsion W
  exact Density.inv_mul_eq_unit' m hm_over
    (Density.genericInclusion_comp (projModelStrCR W.toProjective)) (kwZeroSect R W)
    (kw_lrAddNegDiag_negMor W) hnego
    (kw_ev_e W _ hΔF) (kw_ev_injective W _ hΔF)
    (fun x y hne => kw_ev_pin_map_mul_of_ne W _ hΔF m hmpin x y _ hne)
    (kw_ev_map_one W _ hΔF _)
    (fun x => kw_ev_map_neg W _ hΔF x _)
    hgen2

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul.WeierstrassProjModel.Density"

end S_WeierstrassProjModel_pin_addMorphism_negMor_mul
end P2MW
export P2MW.S_WeierstrassProjModel_pin_addMorphism_negMor_mul (solution)

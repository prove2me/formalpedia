-- Prove2me | solution 1 for WeierstrassProjModel.addMorphism_zeroSect_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ee7cd565-0ed4-560c-ae9d-40d2d3041c63

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_addMorphism_over
import Theorems.Thm_WeierstrassProjModel_kw_a2_map_mul_of_delta_ne_zero
import Theorems.Thm_WeierstrassProjModel_kw_a2_map_one
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul

set_option Elab.async false

section MEGA_prelude2_unitL_lean

end MEGA_prelude2_unitL_lean

section MEGA_DensityKit_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra KwLRSixUCoverage KwLRPerChartCompat projModelAffineOpenCoverCR KwLROuterCompat kw_lrAddMorphism kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval addMorphism_over kw_a2_map_mul_of_delta_ne_zero kw_a2_map_one"
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
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end MEGA_DensityKit_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

section MEGA_DensityIdentities_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra KwLRSixUCoverage KwLRPerChartCompat projModelAffineOpenCoverCR KwLROuterCompat kw_lrAddMorphism kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval addMorphism_over kw_a2_map_mul_of_delta_ne_zero kw_a2_map_one"
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

theorem unit_id_cond : (q ≫ o.1) ≫ q = 𝟙 X ≫ q := by
  rw [Category.assoc, o.2, Category.comp_id, Category.id_comp]

end Points
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

section Triple

variable (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)

end Triple
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

section Identities

variable {q} [IsSeparated q] (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  {P : Type v} [AddCommGroup P]

theorem unit_mul_eq_id [IsIntegral X] [Algebra R X.functionField]
    (halg : genericInclusion X ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)))
    (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q)
    (e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) q → P)
    (he : Function.Injective e)
    (hmul : ∀ x y, e (addPt q m hm x y) = e x + e y)
    (hone : e (onePt q o _) = 0) :
    pullback.lift (q ≫ o.1) (𝟙 X) (unit_id_cond q o) ≫ m = 𝟙 X := by
  let xj : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) q :=
    ⟨genericInclusion X, halg⟩
  have key : addPt q m hm (onePt q o _) xj = xj := he (by rw [hmul, hone, zero_add])
  have hfac : genericInclusion X ≫ pullback.lift (q ≫ o.1) (𝟙 X) (unit_id_cond q o)
      = pullback.lift (onePt q o (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)))).1
          xj.1 ((onePt q o _).2.trans xj.2.symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, xj]
      rw [← Category.assoc, halg]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, xj]
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated q ?_ (genericInclusion X) ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc, Category.id_comp, Category.assoc, o.2,
      Category.comp_id]
  · rw [← Category.assoc, hfac, Category.comp_id]
    exact congrArg Subtype.val key

end Identities
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

section Yoneda

variable {q} (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q)

end Yoneda
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end MEGA_DensityIdentities_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

section MEGA_EvalBridge

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra KwLRSixUCoverage KwLRPerChartCompat projModelAffineOpenCoverCR KwLROuterCompat kw_lrAddMorphism kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval addMorphism_over kw_a2_map_mul_of_delta_ne_zero kw_a2_map_one"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R]

theorem kw_lrAddMorphism_over (W : WeierstrassCurve R)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    kw_lrAddMorphism W hcov hcompat houter ≫ projModelStrCR W.toProjective
      = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective :=
  WeierstrassProjModel.addMorphism_over W hcov hcompat houter

variable (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F]

noncomputable def kw_ev_e (hΔF : algebraMap R F W.Δ ≠ 0) :
    SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective) → (kw_lrApt_WF W F).Point :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose

theorem kw_ev_injective (hΔF : algebraMap R F W.Δ ≠ 0) : Function.Injective (kw_ev_e W F hΔF) :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose_spec.1

theorem kw_ev_point (hΔF : algebraMap R F W.Δ ≠ 0) (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    (kw_ev_e W F hΔF x).point
      = (⟦kw_lrApt_chartEval W F i ψ⟧ : WeierstrassCurve.Projective.PointClass F) :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose_spec.2 x i ψ hfac

theorem kw_ev_factor (hΔF : algebraMap R F W.Δ ≠ 0) (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) :
    ∃ (i : Fin 3) (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F),
      x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).1 x

theorem kw_ev_rechart (hΔF : algebraMap R F W.Δ ≠ 0) (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (k : Fin 3) (hk : kw_lrApt_chartEval W F i ψ k ≠ 0) :
    ∃ ψ' : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F,
      x.1 = Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.1 x i ψ hfac k hk

theorem kw_ev_map_mul (hΔF : algebraMap R F W.Δ ≠ 0)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
    (x y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (h : (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter) ≫ projModelStrCR W.toProjective = kw_lrAptb_tF (R := R) F) :
    kw_ev_e W F hΔF ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter, h⟩
      = kw_ev_e W F hΔF x + kw_ev_e W F hΔF y := by
  obtain ⟨i, ψᵢ, hx⟩ := kw_ev_factor W F hΔF x
  obtain ⟨j, ψⱼ, hy⟩ := kw_ev_factor W F hΔF y
  obtain ⟨k, ψₖ, hs⟩ := kw_ev_factor W F hΔF
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter, h⟩
  apply WeierstrassCurve.Projective.Point.ext
  rw [WeierstrassCurve.Projective.Point.add_point, kw_ev_point W F hΔF _ k ψₖ hs,
    kw_ev_point W F hΔF x i ψᵢ hx, kw_ev_point W F hΔF y j ψⱼ hy]
  exact WeierstrassProjModel.kw_a2_map_mul_of_delta_ne_zero W F hΔF hcov hcompat houter i j ψᵢ ψⱼ k ψₖ x y
    hx hy hs

theorem kw_ev_map_one (hΔF : algebraMap R F W.Δ ≠ 0)
    (h : (kw_lrAptb_tF (R := R) F ≫ (kwZeroSect R W).1) ≫ projModelStrCR W.toProjective = kw_lrAptb_tF (R := R) F) :
    kw_ev_e W F hΔF ⟨kw_lrAptb_tF (R := R) F ≫ (kwZeroSect R W).1, h⟩ = 0 := by
  obtain ⟨k, ψₖ, hs⟩ := kw_ev_factor W F hΔF ⟨kw_lrAptb_tF (R := R) F ≫ (kwZeroSect R W).1, h⟩
  apply WeierstrassCurve.Projective.Point.ext
  rw [WeierstrassCurve.Projective.Point.zero_point, kw_ev_point W F hΔF _ k ψₖ hs]
  exact WeierstrassProjModel.kw_a2_map_one W F k ψₖ hs

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end MEGA_EvalBridge
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

section MEGA_DensityInstances_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra KwLRSixUCoverage KwLRPerChartCompat projModelAffineOpenCoverCR KwLROuterCompat kw_lrAddMorphism kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval addMorphism_over kw_a2_map_mul_of_delta_ne_zero kw_a2_map_one"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section DensityInstances

variable [IsDomain R] [IsNoetherianRing R]
  (hsm : Smooth (projModelStrCR W.toProjective))
  (hgi : GeometricallyIntegral (projModelStrCR W.toProjective))
  (hΔ : IsUnit W.Δ)
  (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "madd" => kw_lrAddMorphism W hcov hcompat houter

include hsm hgi hΔ in

theorem kw_lrDens_unitL :
    pullback.lift (π ≫ (kwZeroSect R W).1) (𝟙 E) (Density.unit_id_cond π (kwZeroSect R W))
      ≫ madd = 𝟙 E := by
  haveI : Smooth π := hsm
  haveI : GeometricallyIntegral π := hgi
  haveI : IsIntegral E := Density.isIntegral_of_smooth_of_geometricallyIntegral π
  letI : Algebra R (E).functionField := Density.functionFieldAlgebra π
  have hΔF : algebraMap R (E).functionField W.Δ ≠ 0 := (hΔ.map _).ne_zero
  exact Density.unit_mul_eq_id madd (kw_lrAddMorphism_over W hcov hcompat houter)
    (Density.genericInclusion_comp π) (kwZeroSect R W)
    (kw_ev_e W _ hΔF) (kw_ev_injective W _ hΔF)
    (fun x y => kw_ev_map_mul W _ hΔF hcov hcompat houter x y _)
    (kw_ev_map_one W _ hΔF _)

end DensityInstances
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

end MEGA_DensityInstances_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel.Density"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul.WeierstrassProjModel in
theorem solution.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback.lift (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1) (𝟙 (projModelCR W.toProjective))
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, Category.id_comp])
      ≫ kw_lrAddMorphism W hcov hcompat houter = 𝟙 (projModelCR W.toProjective) :=
  WeierstrassProjModel.kw_lrDens_unitL W hsm hgi hΔ hcov hcompat houter

end S_WeierstrassProjModel_addMorphism_zeroSect_mul
end P2MW
export P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul (solution)

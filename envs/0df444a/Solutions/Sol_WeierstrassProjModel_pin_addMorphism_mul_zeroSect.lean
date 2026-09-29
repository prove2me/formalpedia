-- Prove2me | solution 1 for WeierstrassProjModel.pin_addMorphism_mul_zeroSect
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/70739451-6836-5452-a36d-1009a6cfaff8

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
import Theorems.Thm_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne
import Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option Elab.async false

section MEGA_DensityKit_lean

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_ne_zero"
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
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end MEGA_DensityKit_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

section MEGA_DensityIdentities_lean

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_ne_zero"
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

theorem unit_id_cond : (q ≫ o.1) ≫ q = 𝟙 X ≫ q := by
  rw [Category.assoc, o.2, Category.comp_id, Category.id_comp]

end Points
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

section Identities

variable {q} [IsSeparated q] (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  {P : Type v} [AddCommGroup P]

theorem mul_unit_eq_id' [IsIntegral X] [Algebra R X.functionField]
    (halg : genericInclusion X ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)))
    (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q)
    (e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) q → P)
    (he : Function.Injective e)
    (hmul : ∀ x y, e x ≠ e y → e (addPt q m hm x y) = e x + e y)
    (hone : e (onePt q o _) = 0)
    (hgen : e ⟨genericInclusion X, halg⟩ ≠ 0) :
    pullback.lift (𝟙 X) (q ≫ o.1) (unit_id_cond q o).symm ≫ m = 𝟙 X := by
  let xj : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) q :=
    ⟨genericInclusion X, halg⟩
  have hne : e xj ≠ e (onePt q o _) := fun h => hgen (h.trans hone)
  have key : addPt q m hm xj (onePt q o _) = xj := he (by rw [hmul _ _ hne, hone, add_zero])
  have hfac : genericInclusion X ≫ pullback.lift (𝟙 X) (q ≫ o.1) (unit_id_cond q o).symm
      = pullback.lift xj.1
          (onePt q o (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)))).1
          (xj.2.trans (onePt q o _).2.symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, xj]
    · simp only [Category.assoc, pullback.lift_snd, xj]
      rw [← Category.assoc, halg]
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated q ?_ (genericInclusion X) ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc]
  · rw [← Category.assoc, hfac, Category.comp_id]
    exact congrArg Subtype.val key

end Identities
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end MEGA_DensityIdentities_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

section MEGA_EvalBridge

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kw_a2_pin_map_mul_of_ne kw_ev_genericPoint_ne_zero"
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
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end MEGA_EvalBridge
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel"
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
      = kw_lrSixU_toE W i j l) :
    pullback.lift (𝟙 (projModelCR W.toProjective))
        (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1)
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, Category.id_comp])
      ≫ m = 𝟙 (projModelCR W.toProjective) := by
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
  have hgen : kw_ev_e W _ hΔF
      ⟨Density.genericInclusion (projModelCR W.toProjective),
        Density.genericInclusion_comp (projModelStrCR W.toProjective)⟩ ≠ 0 :=
    kw_ev_genericPoint_ne_zero W
  exact Density.mul_unit_eq_id' m hm_over
    (Density.genericInclusion_comp (projModelStrCR W.toProjective)) (kwZeroSect R W)
    (kw_ev_e W _ hΔF) (kw_ev_injective W _ hΔF)
    (fun x y hne => kw_ev_pin_map_mul_of_ne W _ hΔF m hmpin x y _ hne)
    (kw_ev_map_one W _ hΔF _)
    hgen

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.WeierstrassProjModel.Density"

end S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect
end P2MW
export P2MW.S_WeierstrassProjModel_pin_addMorphism_mul_zeroSect (solution)

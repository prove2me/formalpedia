-- Prove2me | solution 1 for WeierstrassProjModel.pin_addMorphism_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/eb18083f-e733-57bb-89b5-7ab29e333a4e

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
import Theorems.Thm_WeierstrassProjModel_kw_ev_triple_projections_indep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option Elab.async false

section MEGA_DensityKit_lean

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kw_a2_pin_map_mul_of_ne kw_ev_triple_projections_indep"
namespace Density
p2m_open "WeierstrassProjModel"

universe u

section Integral

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {X : Scheme.{u}}

theorem isIntegral_of_smooth_of_geometricallyIntegral (q : X ⟶ Spec (CommRingCat.of R))
    [Smooth q] [GeometricallyIntegral q] : IsIntegral X :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian q

theorem isIntegral_pullback₂ (q : X ⟶ Spec (CommRingCat.of R))
    [Smooth q] [GeometricallyIntegral q] : IsIntegral ↑(pullback q q) := by
  haveI : IsIntegral X := isIntegral_of_smooth_of_geometricallyIntegral q
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : GeometricallyIntegral (pullback.fst q q) :=
    MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral q›
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst q q)

theorem isIntegral_pullback₃ (q : X ⟶ Spec (CommRingCat.of R))
    [Smooth q] [GeometricallyIntegral q] :
    IsIntegral ↑(pullback (pullback.fst q q ≫ q) q) := by
  haveI : IsIntegral ↑(pullback q q) := isIntegral_pullback₂ q
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : IsLocallyNoetherian ↑(pullback q q) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst q q)
  haveI : GeometricallyIntegral (pullback.fst (pullback.fst q q ≫ q) q) :=
    MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral q›
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
    (pullback.fst (pullback.fst q q ≫ q) q)

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
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end MEGA_DensityKit_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

section MEGA_DensityIdentities_lean

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kw_a2_pin_map_mul_of_ne kw_ev_triple_projections_indep"
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

end Points
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

section Triple

variable (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)

abbrev X3 : Scheme.{u} := pullback (pullback.fst q q ≫ q) q

abbrev fst₃ : X3 q ⟶ pullback q q := pullback.fst (pullback.fst q q ≫ q) q

abbrev snd₃ : X3 q ⟶ X := pullback.snd (pullback.fst q q ≫ q) q

theorem pr₁_over : (fst₃ q ≫ pullback.fst q q) ≫ q = snd₃ q ≫ q :=
  (Category.assoc _ _ _).trans pullback.condition

theorem pr₂_over : (fst₃ q ≫ pullback.snd q q) ≫ q = snd₃ q ≫ q :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition)

def mulLLift : X3 q ⟶ pullback q q :=
  pullback.lift (fst₃ q ≫ m) (snd₃ q)
    (by rw [Category.assoc, hm]; exact pullback.condition)

abbrev mulL : X3 q ⟶ X := mulLLift q m hm ≫ m

def mulRLift : X3 q ⟶ pullback q q :=
  pullback.lift (fst₃ q ≫ pullback.fst q q)
    (pullback.lift (fst₃ q ≫ pullback.snd q q) (snd₃ q) (pr₂_over q) ≫ m)
    (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc]
        exact congrArg (_ ≫ ·) pullback.condition)

abbrev mulR : X3 q ⟶ X := mulRLift q m hm ≫ m

theorem mulL_over : mulL q m hm ≫ q = snd₃ q ≫ q := by
  simp only [mulL, mulLLift, Category.assoc]
  rw [hm, pullback.lift_fst_assoc, Category.assoc, hm]
  exact pullback.condition

theorem mulR_over : mulR q m hm ≫ q = snd₃ q ≫ q := by
  simp only [mulR, mulRLift, Category.assoc]
  rw [hm, pullback.lift_fst_assoc]
  exact (Category.assoc _ _ _).trans pullback.condition

end Triple
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

section Identities

variable {q} [IsSeparated q] (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  {P : Type v} [AddCommGroup P]

theorem mulL_eq_mulR' [IsIntegral ↑(X3 q)] [Algebra R (X3 q).functionField]
    (halg : genericInclusion (X3 q) ≫ snd₃ q ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap R (X3 q).functionField)))
    (e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X3 q).functionField))) q → P)
    (he : Function.Injective e)
    (hmul : ∀ x y, e x ≠ e y → e (addPt q m hm x y) = e x + e y)
    (hindep : ∀ (a b c : P),
      a = e ⟨genericInclusion (X3 q) ≫ fst₃ q ≫ pullback.fst q q,
              by rw [Category.assoc, pr₁_over]; exact halg⟩ →
      b = e ⟨genericInclusion (X3 q) ≫ fst₃ q ≫ pullback.snd q q,
              by rw [Category.assoc, pr₂_over]; exact halg⟩ →
      c = e ⟨genericInclusion (X3 q) ≫ snd₃ q,
              by rw [Category.assoc]; exact halg⟩ →
      a ≠ b ∧ b ≠ c ∧ a + b ≠ c ∧ a ≠ b + c) :
    mulL q m hm = mulR q m hm := by
  let j := genericInclusion (X3 q)
  let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X3 q).functionField))) q :=
    ⟨j ≫ fst₃ q ≫ pullback.fst q q, by
      rw [Category.assoc, pr₁_over]
      exact halg⟩
  let y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X3 q).functionField))) q :=
    ⟨j ≫ fst₃ q ≫ pullback.snd q q, by
      rw [Category.assoc, pr₂_over]
      exact halg⟩
  let z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X3 q).functionField))) q :=
    ⟨j ≫ snd₃ q, by rw [Category.assoc]; exact halg⟩
  obtain ⟨hne_xy, hne_yz, hne_xyz, hne_xyz'⟩ := hindep (e x) (e y) (e z) rfl rfl rfl
  have h2 : e (addPt q m hm x y) = e x + e y := hmul x y hne_xy
  have h4 : e (addPt q m hm y z) = e y + e z := hmul y z hne_yz
  have h1 : e (addPt q m hm (addPt q m hm x y) z) = e (addPt q m hm x y) + e z :=
    hmul _ z (h2 ▸ hne_xyz)
  have h3 : e (addPt q m hm x (addPt q m hm y z)) = e x + e (addPt q m hm y z) :=
    hmul x _ (h4 ▸ hne_xyz')
  have key : addPt q m hm (addPt q m hm x y) z = addPt q m hm x (addPt q m hm y z) :=
    he (by rw [h1, h2, h3, h4, add_assoc])
  have hxyz : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1
        (by rw [pullback.lift_fst_assoc, x.2, z.2]) = j := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp only [Category.assoc, pullback.lift_fst, x]
    · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, y]
    · simp only [pullback.lift_snd, z]
  have hL : j ≫ mulL q m hm = (addPt q m hm (addPt q m hm x y) z).1 := by
    have hfac : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
          ((addPt q m hm x y).2.trans z.2.symm)
        = j ≫ mulLLift q m hm := by
      rw [← hxyz]
      refine pullback.hom_ext ?_ ?_
      · simp only [mulLLift, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [mulLLift, Category.assoc, pullback.lift_snd]
    show j ≫ mulLLift q m hm ≫ m = pullback.lift _ _ _ ≫ m
    rw [← Category.assoc, ← hfac]
  have hR : j ≫ mulR q m hm = (addPt q m hm x (addPt q m hm y z)).1 := by
    have hfac : pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
          (x.2.trans (addPt q m hm y z).2.symm)
        = j ≫ mulRLift q m hm := by
      rw [← hxyz]
      refine pullback.hom_ext ?_ ?_
      · simp only [mulRLift, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [mulRLift, Category.assoc, pullback.lift_snd]
        refine (congrArg (· ≫ m) (pullback.hom_ext ?_ ?_)).trans (Category.assoc _ _ _)
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
            pullback.lift_snd]
        · simp only [Category.assoc, pullback.lift_snd]
    show j ≫ mulRLift q m hm ≫ m = pullback.lift _ _ _ ≫ m
    rw [← Category.assoc, ← hfac]
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated q
    ((mulL_over q m hm).trans (mulR_over q m hm).symm) j ?_
  rw [hL, hR]
  exact congrArg Subtype.val key

end Identities
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end MEGA_DensityIdentities_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

section MEGA_EvalBridge

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "ext_of_isSchemeTheoreticallyDominant_of_isSeparated projModelHomogeneousIdealCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_lrSixU_toE kw_lrSixU_locMap projModelAffineOpenCoverCR kwProjPullbackOpenCoverCR kwProjPullbackChartIsoCR kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval exists_pointEval kw_a2_map_one projModelStrCR_smoothOfRelativeDimension_one kw_hgi_geometricallyIntegral_of_baseChangeIso projModel_pullback_iso_baseChange kw_a2_pin_map_mul_of_ne kw_ev_triple_projections_indep"
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
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end MEGA_EvalBridge
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel"
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

theorem solution
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
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
    pullback.lift
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ m)
        (pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (by rw [Category.assoc, hm_over]; exact pullback.condition)
      ≫ m
    = pullback.lift
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (pullback.lift
            (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
                (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
              ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
            (pullback.snd (pullback.fst (projModelStrCR W.toProjective)
                (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective))
            ((Category.assoc _ _ _).trans
              ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition))
          ≫ m)
        (by rw [Category.assoc, Category.assoc, hm_over, pullback.lift_fst_assoc, Category.assoc]
            exact congrArg (_ ≫ ·) pullback.condition)
      ≫ m := by
  haveI : Smooth (projModelStrCR W.toProjective) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsIntegral ↑(Density.X3 (projModelStrCR W.toProjective)) :=
    Density.isIntegral_pullback₃ (projModelStrCR W.toProjective)
  letI : Algebra R (Density.X3 (projModelStrCR W.toProjective)).functionField :=
    Density.functionFieldAlgebra (Density.snd₃ (projModelStrCR W.toProjective)
      ≫ projModelStrCR W.toProjective)
  have hΔF : algebraMap R (Density.X3 (projModelStrCR W.toProjective)).functionField W.Δ ≠ 0 :=
    (W.isUnit_Δ.map _).ne_zero
  refine Density.mulL_eq_mulR' m hm_over
    (Density.genericInclusion_comp (Density.snd₃ (projModelStrCR W.toProjective)
      ≫ projModelStrCR W.toProjective))
    (kw_ev_e W _ hΔF) (kw_ev_injective W _ hΔF)
    (fun x y hne => kw_ev_pin_map_mul_of_ne W _ hΔF m hmpin x y _ hne)
    ?_

  intro a b c ha hb hc
  have hC := kw_ev_triple_projections_indep (R := R) W
  subst ha; subst hb; subst hc
  exact hC

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc.WeierstrassProjModel.Density"

end S_WeierstrassProjModel_pin_addMorphism_assoc
end P2MW
export P2MW.S_WeierstrassProjModel_pin_addMorphism_assoc (solution)

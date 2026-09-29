-- Prove2me | solution 1 for WeierstrassProjModel.kw_ev_triple_projections_indep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f6339fb6-82d3-5052-aea3-e6898e1fa08b

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_indep

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option Elab.async false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    let X3 : Scheme.{u} :=
      pullback (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
    haveI : IsIntegral X3 := by
      haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
        LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : IsIntegral (projModelCR W.toProjective) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : GeometricallyIntegral (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      haveI : IsIntegral ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : IsLocallyNoetherian ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : GeometricallyIntegral (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    letI : Algebra R X3.functionField :=
      (Spec.preimage (X3.fromSpecStalk (genericPoint X3)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R X3.functionField W.Δ ≠ 0 := (W.isUnit_Δ.map _).ne_zero
    have halg : X3.fromSpecStalk (genericPoint X3)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R X3.functionField)) := by
      show X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective
        = Spec.map (CommRingCat.ofHom (algebraMap R X3.functionField))
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hpr1 : (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)
        ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        ≫ projModelStrCR W.toProjective
      = pullback.snd (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective :=
      (Category.assoc _ _ _).trans pullback.condition
    have hpr2 : (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)
        ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        ≫ projModelStrCR W.toProjective
      = pullback.snd (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective :=
      (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition)
    let e := (exists_pointEval W X3.functionField hΔF).2.2.choose
    let a : (kw_lrApt_WF W X3.functionField).Point :=
      e ⟨X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective),
        by rw [Category.assoc, hpr1]; exact halg⟩
    let b : (kw_lrApt_WF W X3.functionField).Point :=
      e ⟨X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective),
        by rw [Category.assoc, hpr2]; exact halg⟩
    let c : (kw_lrApt_WF W X3.functionField).Point :=
      e ⟨X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective),
        by rw [Category.assoc]; exact halg⟩
    a ≠ b ∧ b ≠ c ∧ a + b ≠ c ∧ a ≠ b + c := by

  haveI : Smooth (projModelStrCR W.toProjective) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  intro X3
  haveI : IsIntegral X3 := by
    haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
      LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
    haveI : IsIntegral (projModelCR W.toProjective) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
    haveI : GeometricallyIntegral (pullback.fst (projModelStrCR W.toProjective)
        (projModelStrCR W.toProjective)) :=
      MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
    haveI : IsIntegral ↑(pullback (projModelStrCR W.toProjective)
        (projModelStrCR W.toProjective)) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    haveI : IsLocallyNoetherian ↑(pullback (projModelStrCR W.toProjective)
        (projModelStrCR W.toProjective)) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    haveI : GeometricallyIntegral (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
        (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
        (projModelStrCR W.toProjective)) :=
      MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
      (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
  letI : Algebra R X3.functionField :=
    (Spec.preimage (X3.fromSpecStalk (genericPoint X3)
      ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
      ≫ projModelStrCR W.toProjective)).hom.toAlgebra
  intro hΔF halg hpr1 hpr2 e a b c

  obtain ⟨ia, ψa, ib, ψb, ic, ψc, hfa, hfb, hfc, hab, hbc, habc, ha_bc⟩ :=
    kw_ev_triple_projections_chartFactor_pointClass_indep W

  have hspec := (exists_pointEval W X3.functionField hΔF).2.2.choose_spec.2
  have hpa : a.point = ⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧ :=
    hspec ⟨_, by rw [Category.assoc, hpr1]; exact halg⟩ ia ψa hfa
  have hpb : b.point = ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧ :=
    hspec ⟨_, by rw [Category.assoc, hpr2]; exact halg⟩ ib ψb hfb
  have hpc : c.point = ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧ :=
    hspec ⟨_, by rw [Category.assoc]; exact halg⟩ ic ψc hfc
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro h
    exact hab (hpa.symm.trans (h ▸ hpb))
  ·
    intro h
    exact hbc (hpb.symm.trans (h ▸ hpc))
  ·
    intro h
    apply habc
    calc (kw_lrApt_WF W X3.functionField).addMap
            ⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
        = (kw_lrApt_WF W X3.functionField).addMap a.point b.point := by rw [hpa, hpb]
      _ = (a + b).point := (WeierstrassCurve.Projective.Point.add_point a b).symm
      _ = c.point := by rw [h]
      _ = ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧ := hpc
  ·
    intro h
    apply ha_bc
    calc (⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
        = a.point := hpa.symm
      _ = (b + c).point := by rw [h]
      _ = (kw_lrApt_WF W X3.functionField).addMap b.point c.point :=
          WeierstrassCurve.Projective.Point.add_point b c
      _ = (kw_lrApt_WF W X3.functionField).addMap
            ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
            ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧ := by rw [hpb, hpc]

end

end S_WeierstrassProjModel_kw_ev_triple_projections_indep
end P2MW
export P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_indep (solution)

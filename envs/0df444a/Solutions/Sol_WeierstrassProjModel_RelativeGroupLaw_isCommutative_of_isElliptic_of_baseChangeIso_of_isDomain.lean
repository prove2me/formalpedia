-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/10169417-34a2-510b-91a5-d68fb4200002

import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_comm_at_field_of_isElliptic_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

noncomputable section

namespace P2mGroupLawCommDom

section Rigidity

variable {R : Type u} [CommRing R]

scoped instance isSeparated_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsSeparated (projModelStrCR V) := by
  unfold projModelStrCR; infer_instance

theorem mul_comm_of_universalPair {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (huniv : G.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      G.mul (pullback.fst f f ≫ f) ⟨pullback.snd f f, pullback.condition.symm⟩ ⟨pullback.fst f f, rfl⟩)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x := by
  set p₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩
  set p₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩
  let ψ : T ⟶ pullback f f := pullback.lift x.1 y.1 (by rw [x.2, y.2])
  have hψ : ψ ≫ (pullback.fst f f ≫ f) = t := by
    rw [← Category.assoc, pullback.lift_fst, x.2]
  have hx : schemeHomOverComp ψ hψ p₁ = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : schemeHomOverComp ψ hψ p₂ = y := Subtype.ext (pullback.lift_snd _ _ _)
  have h₁ := G.mul_natural _ t ψ hψ p₁ p₂
  have h₂ := G.mul_natural _ t ψ hψ p₂ p₁
  rw [hx, hy] at h₁ h₂
  rw [← h₁, ← h₂, huniv]

theorem mul_comm_at_specField (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver q (projModelStrCR V)) :
    G.mul q P Q = G.mul q Q P := by
  letI : Algebra R K := (Spec.preimage q).hom.toAlgebra
  have hq : q = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  clear_value ‹Algebra R K›
  subst hq
  exact RelativeGroupLaw.mul_comm_at_field_of_isElliptic_of_baseChangeIso V hbc G K P Q

theorem mul_comm_of_isReduced_pullback
    (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    [IsReduced (pullback (projModelStrCR V) (projModelStrCR V))]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)) :
    G.mul t x y = G.mul t y x := by
  apply mul_comm_of_universalPair
  apply Subtype.ext
  refine ext_of_fromSpecResidueField_eq _ _ (projModelStrCR V) Set.univ dense_univ (fun z _ => ?_) ?_
  ·
    have e₁ := congrArg Subtype.val (G.mul_natural
      (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V) _
      ((pullback (projModelStrCR V) (projModelStrCR V)).fromSpecResidueField z) rfl
      ⟨pullback.fst (projModelStrCR V) (projModelStrCR V), rfl⟩
      ⟨pullback.snd (projModelStrCR V) (projModelStrCR V), pullback.condition.symm⟩)
    have e₂ := congrArg Subtype.val (G.mul_natural
      (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V) _
      ((pullback (projModelStrCR V) (projModelStrCR V)).fromSpecResidueField z) rfl
      ⟨pullback.snd (projModelStrCR V) (projModelStrCR V), pullback.condition.symm⟩
      ⟨pullback.fst (projModelStrCR V) (projModelStrCR V), rfl⟩)
    simp only [schemeHomOverComp_coe] at e₁ e₂
    rw [e₁, e₂]
    exact congrArg Subtype.val (mul_comm_at_specField V hbc G _ _ _ _)
  · exact ((G.mul _ _ _).2).trans ((G.mul _ _ _).2).symm

theorem mul_comm_of_isDomain [IsDomain R]
    (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)) :
    G.mul t x y = G.mul t y x := by
  haveI : V.IsElliptic := ‹V.toAffine.IsElliptic›
  haveI : SmoothOfRelativeDimension 1 (projModelStrCR V) := projModelStrCR_smoothOfRelativeDimension_one V
  haveI : Smooth (projModelStrCR V) := SmoothOfRelativeDimension.smooth 1 (projModelStrCR V)

  haveI : IsReduced (pullback (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) :=
    isReduced_of_smooth_of_field (pullback.snd _ _)
  haveI : IsReduced (pullback (projModelStrCR V) (projModelStrCR V)) :=
    isReduced_of_flat_of_isReduced_pullback_of_isFractionRing (FractionRing R)
      (pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
  exact mul_comm_of_isReduced_pullback V hbc G t x y

end Rigidity

end P2mGroupLawCommDom
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain.P2mGroupLawCommDom"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain.P2mGroupLawCommDom"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)),
      G.mul t x y = G.mul t y x :=
  fun t x y => P2mGroupLawCommDom.mul_comm_of_isDomain V hbc G t x y

end S_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain (solution)

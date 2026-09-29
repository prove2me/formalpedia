-- Prove2me | solution 1 for WeierstrassProjModel.flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/053dc5b3-4345-544b-b4cf-10dbffdd951b

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two
import Theorems.Thm_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

namespace FlatSchemeFibreEndoSol

section Engine

variable {X : Scheme.{u}} [IsIntegral X]

theorem stalkSpecializes_injective {x y : X} (h : x ⤳ y) :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  have hη : genericPoint X ⤳ x := genericPoint_specializes x
  have hinj : Function.Injective (X.presheaf.stalkSpecializes (hη.trans h)).hom :=
    IsFractionRing.injective (X.presheaf.stalk y) X.functionField
  have hcomp : (X.presheaf.stalkSpecializes hη).hom ∘ (X.presheaf.stalkSpecializes h).hom =
      (X.presheaf.stalkSpecializes (hη.trans h)).hom := by
    funext a
    simp only [Function.comp_apply]
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  refine Function.Injective.of_comp (f := (X.presheaf.stalkSpecializes hη).hom) ?_
  rw [hcomp]
  exact hinj

theorem stalkMap_injective_of_genericPoint (f : X ⟶ X)
    (hη : f (genericPoint X) = genericPoint X) (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have hηx : genericPoint X ⤳ x := genericPoint_specializes x
  have sq := Scheme.Hom.stalkSpecializes_stalkMap f (genericPoint X) x hηx

  have h1 : Function.Injective (f.stalkMap (genericPoint X)).hom := by
    have hF : IsField (X.presheaf.stalk (f (genericPoint X))) := by
      rw [hη]; exact Field.toIsField X.functionField
    intro a b hab
    by_contra hne
    obtain ⟨c, hc⟩ := hF.mul_inv_cancel (sub_ne_zero.mpr hne)
    have h' := congrArg (f.stalkMap (genericPoint X)).hom hc
    rw [map_mul, map_sub, hab, sub_self, zero_mul, map_one] at h'
    exact zero_ne_one h'
  have h2 : Function.Injective
      (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hηx)).hom :=
    stalkSpecializes_injective _
  have h12 := h1.comp h2
  have e : (f.stalkMap (genericPoint X)).hom ∘
      (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hηx)).hom =
      (X.presheaf.stalkSpecializes hηx).hom ∘ (f.stalkMap x).hom := by
    funext a
    simp only [Function.comp_apply]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, sq]
  rw [e] at h12
  exact Function.Injective.of_comp h12

theorem flat_of_valuationRing_stalk (f : X ⟶ X)
    (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hη : f (genericPoint X) = genericPoint X) : Flat f := by
  refine Flat.of_stalkMap f (fun x => ?_)
  have hinj := stalkMap_injective_of_genericPoint f hη x
  haveI := hval (f x)
  letI : Algebra (X.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  show Module.Flat (X.presheaf.stalk (f x)) (X.presheaf.stalk x)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr hinj

end Engine

section Curve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  [IsIntegral C] [SmoothOfRelativeDimension 1 c]

include c in

theorem genericPoint_fixed (f : C ⟶ C) [LocallyQuasiFinite f] :
    f (genericPoint C) = genericPoint C := by
  by_contra hne
  have hcl : IsClosed ({f (genericPoint C)} : Set C) :=
    AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c _ hne
  have hpre : IsClosed (f ⁻¹' {f (genericPoint C)}) := hcl.preimage f.continuous
  have huniv : f ⁻¹' {f (genericPoint C)} = Set.univ := by
    have := ((genericPoint_spec C).mem_closed_set_iff hpre).mp (Set.mem_singleton _)
    exact Set.eq_univ_of_univ_subset this
  have hdisc : _root_.IsDiscrete (f ⁻¹' {f (genericPoint C)}) := f.isDiscrete_preimage_singleton _
  rw [huniv, isDiscrete_univ_iff] at hdisc
  have hmem : f (genericPoint C) ∈ closure ({genericPoint C} : Set C) := by
    rw [genericPoint_closure]; trivial
  rw [closure_discrete] at hmem
  exact hne hmem

end Curve

section Torsion

theorem exists_torsion_point {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ)
    (hℓ : ℓ.Prime) (hℓF : (ℓ : F) ≠ 0) :
    ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0 := by
  haveI : (V.baseChange F).IsElliptic :=
    inferInstanceAs ((V.toAffine.map (algebraMap R F)).IsElliptic)
  have hfin := WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two (K := F)
    (V.baseChange F) hℓ hℓF

  have e : WeierstrassCurve.baseChange (V.baseChange F) F = V.baseChange F := by
    simp [WeierstrassCurve.baseChange]
  have hex : ∃ P : (WeierstrassCurve.baseChange (V.baseChange F) F).toAffine.Point,
      P ≠ 0 ∧ ℓ • P = 0 := by
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    haveI : Nontrivial (Submodule.torsionBy ℤ
        (WeierstrassCurve.baseChange (V.baseChange F) F).toAffine.Point ℓ) :=
      Module.nontrivial_of_finrank_pos (R := ZMod ℓ) (lt_of_lt_of_eq Nat.two_pos hfin.symm)
    obtain ⟨⟨P, hP⟩, hP0⟩ := exists_ne (0 : Submodule.torsionBy ℤ
        (WeierstrassCurve.baseChange (V.baseChange F) F).toAffine.Point ℓ)
    refine ⟨P, fun h0 => hP0 (Subtype.ext h0), ?_⟩
    have := (Submodule.mem_torsionBy_iff _ _).mp hP
    simpa [natCast_zsmul] using this
  rw [e] at hex
  exact hex

end Torsion

end FlatSchemeFibreEndoSol

open FlatSchemeFibreEndoSol in
theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (n : ℕ) (hn : n ≠ 0) (s : Spec (CommRingCat.of R)) :
    Flat (schemeFibreEndo (projModelStrCR V) (G.schemeNsmul n) (G.schemeNsmul_over n) s) := by

  haveI : GeometricallyIntegral (projModelStrCR V) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso (W := V) (projModel_pullback_iso_baseChange V)
  haveI : IsIntegral (pullback (projModelStrCR V)
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)) :=
    inferInstanceAs (IsIntegral ((projModelStrCR V).fiber s))

  haveI : SmoothOfRelativeDimension 1 (projModelStrCR V) :=
    projModelStrCR_smoothOfRelativeDimension_one V
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd (projModelStrCR V)
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  let c : pullback (projModelStrCR V) ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
      Spec (CommRingCat.of ((Spec (CommRingCat.of R)).residueField s)) :=
    pullback.snd (projModelStrCR V) ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  haveI : SmoothOfRelativeDimension 1 c := hsm

  haveI : LocallyQuasiFinite (G.schemeNsmul n) :=
    schemeNsmul_locallyQuasiFinite_of_isPointsEval V (projModel_pullback_iso_baseChange V) G ev
      hev (fun F _ _ _ _ ℓ hℓ hℓF => exists_torsion_point V F ℓ hℓ hℓF) n (Nat.pos_of_ne_zero hn)
  haveI : LocallyQuasiFinite
      (schemeFibreEndo (projModelStrCR V) (G.schemeNsmul n) (G.schemeNsmul_over n) s) := by
    have : LocallyQuasiFinite
        (schemeFibreEndo (projModelStrCR V) (G.schemeNsmul n) (G.schemeNsmul_over n) s ≫
          pullback.fst _ _) := by
      rw [schemeFibreEndo_fst]; infer_instance
    exact LocallyQuasiFinite.of_comp _ (pullback.fst _ _)

  exact flat_of_valuationRing_stalk _
    (fun x => valuationRing_stalk_of_smoothOfRelativeDimension_one c x)
    (genericPoint_fixed c _)

end S_WeierstrassProjModel_flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic (solution)

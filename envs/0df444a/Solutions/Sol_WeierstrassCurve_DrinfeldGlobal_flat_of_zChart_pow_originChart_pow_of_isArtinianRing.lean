-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.flat_of_zChart_pow_originChart_pow_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1ef3dbba-72d5-53e4-929b-a24cf241a8d9

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
import Theorems.Thm_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_locallyQuasiFinite_of_zChart_pow_originChart_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_flat_of_zChart_pow_originChart_pow_of_isArtinianRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FrobFlat

section Inst

variable {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]

scoped instance : IsProper (projModelStrCR V) := WeierstrassProjModel.projModelStrCR_isProper V

scoped instance : SmoothOfRelativeDimension 1 (projModelStrCR V) :=
  haveI : V.IsElliptic := ‹V.toAffine.IsElliptic›
  WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V

scoped instance : GeometricallyIntegral (projModelStrCR V) :=
  WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso (V : WeierstrassCurve R)
    (WeierstrassProjModel.projModel_pullback_iso_baseChange V)

end Inst

theorem flat_pullback_snd_fiberι {T : Type} [CommRing T] (V V' : WeierstrassCurve.Projective T)
    [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (Φ : projModelCR V ⟶ projModelCR V') (hΦ : Φ ≫ projModelStrCR V' = projModelStrCR V) [LocallyQuasiFinite Φ]
    (s : ↥(Spec (CommRingCat.of T))) :
    Flat (pullback.snd Φ ((projModelStrCR V').fiberι s)) := by
  let str := projModelStrCR V
  let str' := projModelStrCR V'
  let K : Type := ↥((Spec (CommRingCat.of T)).residueField s)
  let y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of T) := (Spec (CommRingCat.of T)).fromSpecResidueField s

  let fY : str'.fiber s ⟶ Spec (CommRingCat.of K) := str'.fiberToSpecResidueField s
  have hY : IsPullback (str'.fiberι s) fY str' y := by
    delta Scheme.Hom.fiberι Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber
    exact IsPullback.of_hasPullback _ _

  let g := pullback.snd Φ (str'.fiberι s)
  let fX : pullback Φ (str'.fiberι s) ⟶ Spec (CommRingCat.of K) := g ≫ fY
  have hX : IsPullback (pullback.fst Φ (str'.fiberι s)) fX str y := by
    have := ((IsPullback.of_hasPullback Φ (str'.fiberι s)).flip.paste_horiz hY.flip).flip
    rw [hΦ] at this
    exact this

  haveI : IsIntegral (str'.fiber s) := inferInstance
  haveI : IsIntegral (pullback Φ (str'.fiberι s)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := str) y _ _ hX
  haveI : SmoothOfRelativeDimension 1 fY :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hY inferInstance
  haveI : SmoothOfRelativeDimension 1 fX :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hX inferInstance
  haveI : IsProper fY := MorphismProperty.of_isPullback (P := @IsProper) hY inferInstance
  haveI : IsProper fX := MorphismProperty.of_isPullback (P := @IsProper) hX inferInstance
  haveI : IsSeparated fY := inferInstance
  haveI : LocallyQuasiFinite g := inferInstance
  exact (AlgebraicGeometry.isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
    fX fY 1 g rfl).2.1

end FrobFlat
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_flat_of_zChart_pow_originChart_pow_of_isArtinianRing.FrobFlat"

open FrobFlat in

theorem solution
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective) :
    Flat Φ := by
  haveI hE : (W.toProjective).toAffine.IsElliptic := ⟨hΔ⟩
  haveI hE' : ((W.map (frobenius T q)).toProjective).toAffine.IsElliptic :=
    ⟨by rw [show ((W.map (frobenius T q)).toProjective).toAffine.Δ = (W.map (frobenius T q)).Δ from rfl,
      WeierstrassCurve.map_Δ]; exact hΔ.map _⟩
  haveI : LocallyQuasiFinite Φ :=
    WeierstrassCurve.DrinfeldGlobal.locallyQuasiFinite_of_zChart_pow_originChart_pow q T W Φ hΦ hZ hY
  haveI : Smooth (projModelStrCR W.toProjective) := SmoothOfRelativeDimension.smooth 1 _
  haveI : Smooth (projModelStrCR (W.map (frobenius T q)).toProjective) := SmoothOfRelativeDimension.smooth 1 _
  exact AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
    (projModelStrCR W.toProjective) (projModelStrCR (W.map (frobenius T q)).toProjective) Φ hΦ
    (fun s => flat_pullback_snd_fiberι _ _ Φ hΦ s)

end S_WeierstrassCurve_DrinfeldGlobal_flat_of_zChart_pow_originChart_pow_of_isArtinianRing
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_flat_of_zChart_pow_originChart_pow_of_isArtinianRing (solution)

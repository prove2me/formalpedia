-- Prove2me | solution 1 for WeierstrassCurve.apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5c98ca23-d61b-5169-979e-4a3023cb480d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
import Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare nonempty_modularPolynomialData"
namespace ModularPolynomialData
p2m_export "ModularCurve.ModularPolynomialData" "Φ isUnit_leadingCoeff_diag_of_not_isSquare"
namespace GenericNoCM
p2m_open "ModularCurve.ModularPolynomialData ModularCurve"

open Polynomial

section Transcendence

variable {k : Type*} [Field k]

theorem constantCoeff_aeval_of_constantCoeff_eq_zero (u : PowerSeries k)
    (hu : PowerSeries.constantCoeff u = 0) (q : k[X]) :
    PowerSeries.constantCoeff (aeval u q) = q.coeff 0 := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hu, Polynomial.coeff_zero_eq_eval_zero]
  have hcomp : (PowerSeries.constantCoeff (R := k)).comp (algebraMap k (PowerSeries k))
      = RingHom.id k := by
    ext a
    simp
  rw [hcomp]
  rfl

theorem transcendental_of_ne_C (f : PowerSeries k)
    (hf : f ≠ PowerSeries.C (PowerSeries.constantCoeff f)) : Transcendental k f := by
  intro halg
  set c : k := PowerSeries.constantCoeff f with hc
  set u : PowerSeries k := f - PowerSeries.C c with hu
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    simp [hu, hc]
  have hune : u ≠ 0 := sub_ne_zero.mpr hf
  have halgu : IsAlgebraic k u := by
    rw [isAlgebraic_iff_isIntegral] at halg ⊢
    have hcst : IsIntegral k (PowerSeries.C c : PowerSeries k) := by
      have : (PowerSeries.C c : PowerSeries k) = algebraMap k (PowerSeries k) c := rfl
      rw [this]
      exact isIntegral_algebraMap
    exact halg.sub hcst
  obtain ⟨P, hP0, hPu⟩ := halgu
  obtain ⟨Q, hPQ, hQ⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 0
  rw [map_zero, sub_zero] at hPQ hQ
  rw [Polynomial.X_dvd_iff] at hQ
  have hQu : aeval u Q ≠ 0 := by
    intro h0
    apply hQ
    rw [← constantCoeff_aeval_of_constantCoeff_eq_zero u hu0 Q, h0, map_zero]
  have hfac : aeval u P = u ^ P.rootMultiplicity 0 * aeval u Q := by
    conv_lhs => rw [hPQ]
    rw [map_mul, map_pow, Polynomial.aeval_X]
  rw [hfac] at hPu
  rcases mul_eq_zero.mp hPu with h1 | h2
  · exact hune (pow_eq_zero_iff'.mp h1).1
  · exact hQu h2

end Transcendence

section Diagonal

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem eval_map_self_eq_eval₂_diag (Φ : Polynomial (Polynomial ℤ)) (x : R) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)).eval x
      = (Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).eval₂ (Int.castRingHom R) x := by
  rw [Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ Φ (RingHom.id (Polynomial ℤ))
    (Polynomial.eval₂RingHom (Int.castRingHom R) x) Polynomial.X
  rw [Polynomial.coe_eval₂RingHom] at h
  rw [h, RingHom.comp_id, Polynomial.eval₂_X]

theorem eval₂_intCast_eq_aeval_map (D : Polynomial ℤ) (x : R) :
    D.eval₂ (Int.castRingHom R) x = aeval x (D.map (Int.castRingHom K)) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem map_ne_zero_of_isUnit_leadingCoeff {D : Polynomial ℤ} (hD : IsUnit D.leadingCoeff) :
    D.map (Int.castRingHom K) ≠ 0 := by
  have hlead : (Int.castRingHom K) D.leadingCoeff ≠ 0 := (hD.map (Int.castRingHom K)).ne_zero
  intro h0
  have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (Int.castRingHom K) hlead
  rw [h0, Polynomial.leadingCoeff_zero] at this
  exact hlead this.symm

theorem eval_map_diag_ne_zero_of_transcendental {N : ℕ} [NeZero N] (hN : ¬ IsSquare N)
    (data : ModularCurve.ModularPolynomialData N) {x : R} (hx : Transcendental K x) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)).eval x ≠ 0 := by
  rw [eval_map_self_eq_eval₂_diag, eval₂_intCast_eq_aeval_map (K := K)]
  intro h0
  exact hx ⟨_, map_ne_zero_of_isUnit_leadingCoeff
    (ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare N hN data), h0⟩

end Diagonal

end ModularCurve.ModularPolynomialData.GenericNoCM

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map Affine.CoordinateRing map_j reduction IsIntegral toAffine Δ j veluQuotient oddOrderSummingSet Affine.pointMapOfPushforward Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq Affine.hasPrincipalDivisors_of_isAlgClosed Affine.CoordinateRing.isDedekindDomain Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem"
namespace GenericDeformationNoCM
p2m_open "WeierstrassCurve"

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C.WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve"

theorem map_eval_map_modularPolynomial {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (Φ : Polynomial (Polynomial ℤ)) (a b : A) :
    f ((Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) a)).eval b)
      = (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom B) (f a))).eval (f b) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun z => ?_) ?_
  · simp
  · simp

theorem eval_modularPolynomial_j_veluQuotient_eq_zero
    {L : Type} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (W : WeierstrassCurve L) [W.IsElliptic] {n : ℕ} (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) W.j)).eval
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = 0 := by
  haveI hW' : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  haveI : IsDedekindDomain W.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain W
  haveI : IsDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI hPD : AlgebraicCurve.HasPrincipalDivisors L W.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed W.toAffine
  haveI hPD' : AlgebraicCurve.HasPrincipalDivisors L
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed _

  obtain ⟨g, hg, ha⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)
  letI : WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine := g
  haveI : WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine := hg
  haveI : WeierstrassCurve.Affine.AbelTheorem W.toAffine := ha
  obtain ⟨g', hg', ha'⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
      (W := (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine)
  letI : WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine := g'
  haveI : WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine := hg'
  haveI : WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine := ha'

  obtain ⟨ι, hι, hfin, -, hker, -, -⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq hQ hΔ

  haveI : CharZero (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap L _).injective
  have hsep : AlgebraicCurve.SeparableAlong L ι := AlgebraicCurve.separableAlong_of_charZero ι hι
  have hN : AlgebraicCurve.NormFormulaAlong L ι hfin := AlgebraicCurve.normFormulaAlong ι hfin hsep
  have hk := hker hN
  have hcyc : IsAddCyclic (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker := by
    rw [hk]
    infer_instance
  have hcard : Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = 2 * n + 1 := by
    rw [hk, Nat.card_zmultiples, hQ]
  exact WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
    L W.toAffine (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine ι hι hfin hN (2 * n + 1)
    hcyc hcard data

end WeierstrassCurve.GenericDeformationNoCM

open WeierstrassCurve.GenericDeformationNoCM ModularCurve.ModularPolynomialData.GenericNoCM in

theorem solution
    {S : Type*} [CommRing S] (E E' : WeierstrassCurve S) [E.IsElliptic] [E'.IsElliptic]
    {L : Type} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (φ : S →+* L) (hφ : Function.Injective φ)
    {n : ℕ} (hn : ¬ IsSquare (2 * n + 1))
    (Q : (E.map φ).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : ((E.map φ).veluQuotient ((E.map φ).oddOrderSummingSet Q n)).Δ ≠ 0)
    (hE' : haveI : ((E.map φ).veluQuotient ((E.map φ).oddOrderSummingSet Q n)).IsElliptic :=
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      (E'.map φ).j = ((E.map φ).veluQuotient ((E.map φ).oddOrderSummingSet Q n)).j)
    {k : Type*} [Field k] (ρ : S →+* PowerSeries k)
    (hj : ρ E.j ≠ PowerSeries.C (PowerSeries.constantCoeff (ρ E.j))) :
    ρ E'.j ≠ ρ E.j := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData (2 * n + 1)

  have hL := eval_modularPolynomial_j_veluQuotient_eq_zero (E.map φ) Q hQ hΔ data
  rw [← hE', WeierstrassCurve.map_j, WeierstrassCurve.map_j, ← map_eval_map_modularPolynomial]
    at hL

  have hS : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) E.j)).eval E'.j = 0 :=
    hφ (by rw [hL, map_zero])
  have hk : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries k)) (ρ E.j))).eval
      (ρ E'.j) = 0 := by
    rw [← map_eval_map_modularPolynomial, hS, map_zero]
  intro heq
  rw [heq] at hk
  exact eval_map_diag_ne_zero_of_transcendental (K := k) hn data
    (transcendental_of_ne_C (ρ E.j) hj) hk

end S_WeierstrassCurve_apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C
end P2MW
export P2MW.S_WeierstrassCurve_apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C (solution)

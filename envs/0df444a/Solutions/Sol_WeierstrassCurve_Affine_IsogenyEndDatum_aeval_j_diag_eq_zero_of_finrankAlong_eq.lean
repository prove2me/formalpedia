-- Prove2me | solution 1 for WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/19ad62a3-f786-52d3-87d0-a6dda5e2bda1

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePic0
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq
import Theorems.Thm_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq
import Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
import Theorems.Thm_IsAddCyclic_of_squarefree_natCard
import Theorems.Thm_PeriodPair_jLattice_surjective
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Theorems.Thm_PeriodPair_isUniformization_toPoint
import Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
import Theorems.Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
import Theorems.Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

universe u

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic"
p2m_open "ModularCurve"
open Cardinal IntermediateField

private def kw_d5eu_ratEquivStrip {A B : Type*} [Semiring A] [Semiring B]
    {iA : Algebra ℚ A} {iB : Algebra ℚ B} (e : @AlgEquiv ℚ A B _ _ _ iA iB) :
    A ≃+* B :=
  @AlgEquiv.toRingEquiv ℚ A B _ _ _ iA iB e

theorem kw_countable_algebraicClosure (K₀ : Type u) [Field K₀] [Countable K₀] :
    Countable (AlgebraicClosure K₀) :=
  Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max K₀ (AlgebraicClosure K₀)).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))

theorem kw_aleph0_lt_mk_transcendenceBasis_complex
    {t : Set ℂ} (ht : IsTranscendenceBasis ℚ ((↑) : t → ℂ)) : ℵ₀ < #t := by
  rw [← not_le]
  intro h
  haveI : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) ℂ := ht.isAlgebraic_field
  have hadj : #(IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) ≤ ℵ₀ :=
    (IntermediateField.cardinalMk_adjoin_le ℚ _).trans
      (max_le (max_le Cardinal.mk_le_aleph0 (Cardinal.mk_range_le.trans h)) le_rfl)
  have hℂ : #ℂ ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max _ ℂ).trans (max_le hadj le_rfl)
  exact absurd hℂ <| not_le.mpr <| Cardinal.aleph0_lt_continuum.trans_le
    (Cardinal.mk_real ▸ Cardinal.mk_le_of_injective Complex.ofReal_injective)

set_option synthInstance.maxHeartbeats 6400000 in
theorem kw_nonempty_ringHom_algebraicClosure_complex (K₀ : Type u) [Field K₀] [Algebra ℚ K₀]
    [Countable K₀] : Nonempty (AlgebraicClosure K₀ →+* ℂ) := by
  let ACK := AlgebraicClosure K₀
  haveI : Countable ACK := kw_countable_algebraicClosure K₀
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (A := ACK)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ (A := ℂ)

  have hcard : Cardinal.lift.{0, u} #s ≤ Cardinal.lift.{u, 0} #t := by
    have h1 : Cardinal.lift.{0, u} #s ≤ ℵ₀ := Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0
    have h2 : ℵ₀ ≤ Cardinal.lift.{u, 0} #t :=
      Cardinal.aleph0_le_lift.mpr (le_of_lt (kw_aleph0_lt_mk_transcendenceBasis_complex ht))
    exact h1.trans h2
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hcard
  have hf_indep : AlgebraicIndependent ℚ (fun i : s => ((f i : t) : ℂ)) :=
    ht.1.comp f f.injective
  let Qs : IntermediateField ℚ ACK := adjoin ℚ (Set.range ((↑) : s → ACK))
  let φQs : Qs →+* ℂ :=
    ((adjoin ℚ (Set.range (fun i : s => ((f i : t) : ℂ)))).val.toRingHom.comp
      (kw_d5eu_ratEquivStrip hf_indep.aevalEquivField).toRingHom).comp
        (kw_d5eu_ratEquivStrip hs.1.aevalEquivField).symm.toRingHom
  letI : Algebra Qs ℂ := φQs.toAlgebra
  haveI : Algebra.IsAlgebraic Qs ACK := hs.isAlgebraic_field
  exact ⟨(IsAlgClosed.lift (R := Qs) (M := ℂ) (S := ACK)).toRingHom⟩

end ModularCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY variableChange_j a₃ a₁ map Affine.CoordinateRing coe_Δ' map_j mk Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some baseChange j exists_intermediateField_countable_map_eq_and_finrankAlong_eq Affine.exists_algHom_functionField_baseChange_finrankAlong_eq Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong nonempty_functionField_algEquiv_of_variableChange Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem Affine.CoordinateRing.isDedekindDomain Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "negY CoordinateRing map baseChange Point.some Point.some.injEq FunctionField Point polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum exists_algHom_functionField_baseChange_finrankAlong_eq natCard_ker_pointMapOfPushforward_eq_finrankAlong exists_genusOnePlaceGate_isCentred_and_abelTheorem CoordinateRing.isDedekindDomain hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

open AlgebraicCurve

scoped instance instHasPrincipalDivisorsFunctionField_s13 {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

section AutoNorm
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) : NormFormulaAlong F ι hfin := by
  haveI : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField W
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite V.FunctionField W.FunctionField := hfin
    show Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

end AutoNorm

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve"

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic"
p2m_open "ModularCurve"
p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine AlgebraicCurve"

section ConjHelpers

variable {K : Type*} [Field K]
variable {E E' F F' : WeierstrassCurve.Affine K}

def kw_fdn2_qephod_hend21_conjSeam
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    F'.FunctionField →ₐ[K] F.FunctionField :=
  (eE.symm.toAlgHom.comp ι).comp eE'.toAlgHom

theorem kw_fdn2_qephod_hend21_conjSeam_isIntegral
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) :
    (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans eE'.toAlgHom.toRingHom (eE.symm.toAlgHom.comp ι).toRingHom
    (RingHom.isIntegral_of_surjective _ eE'.surjective)
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (RingHom.isIntegral_of_surjective _ eE.symm.surjective))

theorem kw_fdn2_qephod_hend21_conjSeam_finiteAlong
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    FiniteAlong K (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) := by
  have hfin' : RingHom.Finite ι.toRingHom := hfin
  have h1 : RingHom.Finite eE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE'.surjective
  have h2 : RingHom.Finite eE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE.symm.surjective
  have hcomp : RingHom.Finite
      (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom :=
    RingHom.Finite.comp (g := (eE.symm.toAlgHom.comp ι).toRingHom)
      (RingHom.Finite.comp (g := eE.symm.toAlgHom.toRingHom) h2 hfin') h1
  exact hcomp

theorem kw_fdn2_qephod_hend21_finrankAlong_conj
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    finrankAlong K (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) = finrankAlong K ι := by
  refine @Algebra.finrank_eq_of_equiv_equiv F'.FunctionField F.FunctionField _ _
    (algebraAlong (kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    E'.FunctionField E.FunctionField _ _ (algebraAlong ι)
    eE'.toRingEquiv eE.toRingEquiv (RingHom.ext fun x => ?_)
  show ι (eE' x) = eE (eE.symm (ι (eE' x)))
  exact (eE.apply_symm_apply _).symm

end ConjHelpers
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

end ModularCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section
open Complex Filter Set

p2m_open_scoped "PeriodPair P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "derivWeierstrassP_neg weierstrassP_neg lattice weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk g₃ ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₃ DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem IsUniformization jLattice jLattice_eq_c₄_pow_three_div_Δ scale_indep scale discriminant_ne_zero isUniformization_toPoint exists_variableChange_smul_weierstrassCurve_eq exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private theorem _root_.PeriodPair.kw_discriminantNeZero : L.DiscriminantNeZero := L.discriminant_ne_zero

p2m_export "PeriodPair" "kw_discriminantNeZero"

private theorem _root_.PeriodPair.kw_isUniformization : L.IsUniformization L.kw_discriminantNeZero :=
  L.isUniformization_toPoint _

p2m_export "PeriodPair" "kw_isUniformization"

private theorem _root_.PeriodPair.kw_toPoint_add (hD : L.DiscriminantNeZero) (z w : ℂ) :
    L.toPoint hD (z + w) = L.toPoint hD z + L.toPoint hD w :=
  (L.isUniformization_toPoint hD).1 z w

p2m_export "PeriodPair" "kw_toPoint_add"

theorem kw_toPoint_surjective (hD : L.DiscriminantNeZero) : Function.Surjective (L.toPoint hD) :=
  (L.isUniformization_toPoint hD).2.1

theorem kw_toPoint_eq_zero_iff (hD : L.DiscriminantNeZero) (z : ℂ) :
    L.toPoint hD z = 0 ↔ z ∈ L.lattice :=
  ⟨(L.isUniformization_toPoint hD).2.2 z, fun hz => L.toPoint_of_mem hD hz⟩

scoped instance kw_instIsElliptic : L.weierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr L.kw_discriminantNeZero.weierstrassCurve_Δ_ne_zero⟩

section Liouville

private theorem _root_.PeriodPair.sub_fract_mem_lattice (z : ℂ) : z - ZSpan.fract L.basis z ∈ L.lattice := by
  rw [L.lattice_eq_span_range_basis]
  have h := (ZSpan.fract_eq_fract L.basis (ZSpan.fract L.basis z) z).mp
    (by rw [ZSpan.fract_eq_self.mpr (ZSpan.fract_mem_fundamentalDomain L.basis z)])
  simpa [neg_add_eq_sub] using h

p2m_export "PeriodPair" "sub_fract_mem_lattice"

private theorem _root_.PeriodPair.apply_eq_apply_of_differentiable_of_forall_periodic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ l ∈ L.lattice, ∀ z, f (z + l) = f z) (z w : ℂ) :
    f z = f w := by
  apply hf.apply_eq_apply_of_bounded

  have hrange : range f ⊆ f '' closure (ZSpan.fundamentalDomain L.basis) := by
    rintro - ⟨u, rfl⟩
    refine ⟨ZSpan.fract L.basis u, subset_closure (ZSpan.fract_mem_fundamentalDomain _ u), ?_⟩
    have h := hper _ (L.sub_fract_mem_lattice u) (ZSpan.fract L.basis u)
    rw [add_sub_cancel] at h
    exact h.symm

  refine Bornology.IsBounded.subset ?_ hrange
  refine (IsCompact.image ?_ hf.continuous).isBounded
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (ZSpan.fundamentalDomain_isBounded L.basis).closure

p2m_export "PeriodPair" "apply_eq_apply_of_differentiable_of_forall_periodic"
end Liouville
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

section ToPointLemmas

theorem toPoint_add_mem (h : L.DiscriminantNeZero) (z : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    L.toPoint h (z + l) = L.toPoint h z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem h hz, L.toPoint_of_mem h (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun hmem => hz (by simpa using sub_mem hmem hl)
    rw [L.toPoint_of_notMem h hz, L.toPoint_of_notMem h hzl]
    have hP : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
    have hP' : ℘'[L] (z + l) = ℘'[L] z := L.derivWeierstrassP_add_coe z ⟨l, hl⟩
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hP, by rw [hP']⟩

theorem toPoint_neg (h : L.DiscriminantNeZero) (z : ℂ) :
    L.toPoint h (-z) = -L.toPoint h z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem h hz, L.toPoint_of_mem h (neg_mem hz)]; rfl
  · have hnz : -z ∉ L.lattice := fun hmem => hz (by simpa using neg_mem hmem)
    rw [L.toPoint_of_notMem h hz, L.toPoint_of_notMem h hnz,
      WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨L.weierstrassP_neg z, ?_⟩
    rw [L.derivWeierstrassP_neg]
    show -℘'[L] z / 2 = L.weierstrassCurve.toAffine.negY (℘[L] z) (℘'[L] z / 2)
    rw [WeierstrassCurve.Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring

end ToPointLemmas
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

section Isogeny

private theorem _root_.PeriodPair.apply_eq_apply_of_continuous_of_mapsTo_lattice {f : ℂ → ℂ} (hf : Continuous f)
    (hmem : ∀ z, f z ∈ L.lattice) (z w : ℂ) : f z = f w := by
  refine IsPreconnected.constant_of_mapsTo (isPreconnected_univ) ?_
    hf.continuousOn (fun u _ => hmem u) (mem_univ z) (mem_univ w)
  rw [isDiscrete_iff_discreteTopology]
  exact inferInstanceAs (DiscreteTopology L.lattice)

p2m_export "PeriodPair" "apply_eq_apply_of_continuous_of_mapsTo_lattice"

theorem exists_smul_mem_and_apply_eq_of_forall_sub_mem (L' : PeriodPair) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (hper : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z ∈ L'.lattice) :
    ∃ α : ℂ, (∀ l ∈ L.lattice, α * l ∈ L'.lattice) ∧ ∀ z, F z = F 0 + α * z := by

  have hFc : Continuous F := hF.continuous
  have hconst : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z = F l - F 0 := by
    intro l hl z
    have h := L'.apply_eq_apply_of_continuous_of_mapsTo_lattice
      (f := fun u => F (u + l) - F u)
      ((hFc.comp (continuous_id.add continuous_const)).sub hFc) (hper l hl) z 0
    simpa using h

  have hadd : ∀ z w, F (z + w) = F z + F w - F 0 := by
    intro z w
    have hper' : ∀ l ∈ L.lattice, ∀ u,
        (fun u => F (u + w) - F u) (u + l) = (fun u => F (u + w) - F u) u := by
      intro l hl u
      have h1 := hconst l hl (u + w)
      have h2 := hconst l hl u
      rw [show u + w + l = u + l + w by ring] at h1
      simp only
      linear_combination h1 - h2
    have h := L.apply_eq_apply_of_differentiable_of_forall_periodic
      (f := fun u => F (u + w) - F u)
      ((hF.comp (differentiable_id.add_const w)).sub hF) hper' z 0
    simp only [zero_add] at h
    linear_combination h

  set α : ℂ := deriv F 0 with hα
  have hderiv : ∀ z, deriv F z = α := by
    intro z
    have hfun : (fun w => F (z + w)) = fun w => F w + (F z - F 0) := by
      funext w
      rw [hadd z w]; ring
    have h1 : deriv (fun w => F (z + w)) 0 = deriv F z := by
      rw [deriv_comp_const_add]
      simp
    have h2 : deriv (fun w => F w + (F z - F 0)) 0 = deriv F 0 := by
      rw [deriv_add_const]
    rw [← h1, hfun, h2]

  have haffine : ∀ z, F z = F 0 + α * z := by
    have hG : Differentiable ℂ fun z => F z - α * z :=
      hF.sub (differentiable_id.const_mul α)
    have hG' : ∀ z, deriv (fun z => F z - α * z) z = 0 := by
      intro z
      have hd : HasDerivAt (fun z => F z - α * z) (deriv F z - α * 1) z :=
        (hF z).hasDerivAt.sub ((hasDerivAt_id z).const_mul α)
      rw [hd.deriv, hderiv z]
      ring
    intro z
    have h := is_const_of_deriv_eq_zero hG hG' z 0
    simp only [mul_zero, sub_zero] at h
    linear_combination h

  refine ⟨α, fun l hl => ?_, haffine⟩
  have h := hper l hl 0
  rw [zero_add, haffine l] at h
  simpa using h

end Isogeny
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

section Scale

variable (α : ℂˣ)

private def mulLeftR (a : ℂ) : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ a

@[scoped simp] private theorem mulLeftR_apply (a z : ℂ) : mulLeftR a z = a * z := rfl

private theorem mulLeftR_injective {a : ℂ} (ha : a ≠ 0) :
    Function.Injective (mulLeftR a) := fun _ _ h => by
  simpa using mul_left_cancel₀ ha h

private def mulLeftZ (a : ℂ) : ℂ →ₗ[ℤ] ℂ := (mulLeftR a).restrictScalars ℤ

@[scoped simp] private theorem mulLeftZ_apply (a z : ℂ) : mulLeftZ a z = a * z := rfl

private theorem _root_.PeriodPair.scale_lattice : (L.scale α).lattice = Submodule.map (mulLeftZ (α : ℂ)) L.lattice := by
  unfold lattice scale
  rw [Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, mulLeftZ_apply]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨L.ω₁, Or.inl rfl, rfl⟩
    · exact ⟨L.ω₂, Or.inr rfl, rfl⟩
  · rintro ⟨w, hw | hw, rfl⟩ <;> simp [hw]

p2m_export "PeriodPair" "scale_lattice"
theorem mem_scale_lattice_iff {z : ℂ} :
    z ∈ (L.scale α).lattice ↔ ∃ l ∈ L.lattice, z = (α : ℂ) * l := by
  rw [scale_lattice, Submodule.mem_map]; simp only [mulLeftZ_apply]; tauto

private def _root_.PeriodPair.scaleLatticeEquiv : L.lattice ≃ₗ[ℤ] (L.scale α).lattice :=
  (Submodule.equivMapOfInjective (mulLeftZ (α : ℂ))
    (fun _ _ h => mul_left_cancel₀ α.ne_zero (by simpa using h)) L.lattice).trans
    (LinearEquiv.ofEq _ _ (L.scale_lattice α).symm)

p2m_export "PeriodPair" "scaleLatticeEquiv"
@[scoped simp] theorem scaleLatticeEquiv_apply (l : L.lattice) :
    ((L.scaleLatticeEquiv α l : (L.scale α).lattice) : ℂ) = (α : ℂ) * (l : ℂ) := rfl

end Scale
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

section Homogeneity

variable (α : ℂˣ)

theorem G_scale (n : ℕ) : (L.scale α).G n = ((α : ℂ) ^ n)⁻¹ * L.G n := by
  unfold G
  rw [← (L.scaleLatticeEquiv α).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, scaleLatticeEquiv_apply, mul_pow, mul_inv]
  exact tsum_mul_left

theorem g₂_scale : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  unfold g₂; rw [G_scale]; ring

theorem g₃_scale : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  unfold g₃; rw [G_scale]; ring

theorem discriminant_scale :
    (L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2
      = ((α : ℂ) ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [g₂_scale, g₃_scale]; ring

theorem g₂_cubed_scale : (L.scale α).g₂ ^ 3 = ((α : ℂ) ^ 12)⁻¹ * L.g₂ ^ 3 := by
  rw [g₂_scale, mul_pow, inv_pow, ← pow_mul]

theorem jLattice_scale : (L.scale α).jLattice = L.jLattice := by
  have hα : ((α : ℂ) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ α.ne_zero)
  unfold jLattice
  rw [discriminant_scale, g₂_cubed_scale, mul_left_comm (1728 : ℂ), mul_div_mul_left _ _ hα]

theorem discriminantNeZero_scale_iff :
    (L.scale α).DiscriminantNeZero ↔ L.DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [discriminant_scale]
  simp only [mul_ne_zero_iff, and_iff_right (inv_ne_zero (pow_ne_zero 12 α.ne_zero))]

end Homogeneity
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

section LatticeDependence

variable {L L' : PeriodPair}

private def latticeEquivOfEq (h : L.lattice = L'.lattice) : L.lattice ≃ L'.lattice where
  toFun l := ⟨(l : ℂ), h ▸ l.2⟩
  invFun l := ⟨(l : ℂ), h.symm ▸ l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem G_eq_of_lattice_eq (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n :=
  (latticeEquivOfEq h).tsum_eq fun l => ((l : ℂ) ^ n)⁻¹

theorem g₂_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ := by
  unfold g₂; rw [G_eq_of_lattice_eq h]

theorem g₃_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ := by
  unfold g₃; rw [G_eq_of_lattice_eq h]

theorem jLattice_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.jLattice = L'.jLattice := by
  unfold jLattice; rw [g₂_eq_of_lattice_eq h, g₃_eq_of_lattice_eq h]

end LatticeDependence
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

section Gates

theorem gate_scale_mul (α β : ℂˣ) :
    ((L.scale α).scale β).lattice = (L.scale (β * α)).lattice := by
  ext z
  simp only [mem_scale_lattice_iff, Units.val_mul]
  constructor
  · rintro ⟨-, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, (mul_assoc _ _ _).symm⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨(α : ℂ) * l, ⟨l, hl, rfl⟩, mul_assoc _ _ _⟩

end Gates
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine"

private theorem _root_.PeriodPair.kw_countable_lattice : (L.lattice : Set ℂ).Countable := by
  refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
  intro z hz
  obtain ⟨m, n, h⟩ := mem_lattice.mp hz
  exact ⟨(m, n), h⟩

p2m_export "PeriodPair" "kw_countable_lattice"

private def _root_.PeriodPair.kw_toPointHom : ℂ →+ (L.weierstrassCurve.toAffine).Point where
  toFun := L.toPoint L.kw_discriminantNeZero
  map_zero' := L.toPoint_zero L.kw_discriminantNeZero
  map_add' := L.kw_toPoint_add L.kw_discriminantNeZero

p2m_export "PeriodPair" "kw_toPointHom"
theorem kw_toPointHom_apply (z : ℂ) :
    L.kw_toPointHom z = L.toPoint L.kw_discriminantNeZero z := rfl

private theorem _root_.PeriodPair.kw_ker_toPointHom :
    L.kw_toPointHom.ker = L.lattice.toAddSubgroup := by
  ext z
  constructor
  · exact fun hz => (L.kw_isUniformization).2.2 z hz
  · intro hz
    exact L.toPoint_of_mem L.kw_discriminantNeZero hz

p2m_export "PeriodPair" "kw_ker_toPointHom"

private def _root_.PeriodPair.kw_toPointAddEquiv : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (L.weierstrassCurve.toAffine).Point :=
  QuotientAddGroup.liftEquiv L.lattice.toAddSubgroup (φ := L.kw_toPointHom)
    (L.kw_isUniformization).2.1 L.kw_ker_toPointHom.symm

p2m_export "PeriodPair" "kw_toPointAddEquiv"
theorem kw_toPointAddEquiv_mk (z : ℂ) :
    L.kw_toPointAddEquiv (QuotientAddGroup.mk z) = L.toPoint L.kw_discriminantNeZero z :=
  rfl

scoped instance kw_infinite_quotientLattice : Infinite (ℂ ⧸ L.lattice.toAddSubgroup) := by
  rw [← not_finite_iff_infinite]; intro hfin
  haveI : Countable L.lattice.toAddSubgroup :=
    Set.countable_coe_iff.mpr L.kw_countable_lattice
  haveI : Countable ((ℂ ⧸ L.lattice.toAddSubgroup) × L.lattice.toAddSubgroup) := inferInstance
  have hCc : Countable ℂ :=
    Countable.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup
      (s := L.lattice.toAddSubgroup)).symm
  haveI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact absurd hCc not_countable

scoped instance kw_infinite_point : Infinite L.weierstrassCurve.toAffine.Point :=
  L.kw_toPointAddEquiv.toEquiv.infinite_iff.mp inferInstance

end PeriodPair
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.PeriodPair"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.PeriodPair"

theorem s13_aeval_diag_eq_eval_map {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    Polynomial.aeval a (Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X)
      = (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).eval a := by
  let lhs : Polynomial (Polynomial ℤ) →+* R :=
    (Polynomial.aeval (R := ℤ) a).toRingHom.comp (Polynomial.eval₂RingHom (RingHom.id (Polynomial ℤ)) Polynomial.X)
  let rhs : Polynomial (Polynomial ℤ) →+* R :=
    (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom R) a))
  have h : lhs = rhs := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [lhs, rhs, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        RingHom.id_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map]
      simp [Polynomial.eval₂_eq_eval_map]
    · simp [lhs, rhs]
  exact RingHom.congr_fun h Φ

theorem s13_j_weierstrassCurve_eq_jLattice (L : PeriodPair) [L.weierstrassCurve.IsElliptic] :
    L.weierstrassCurve.j = L.jLattice := by
  rw [PeriodPair.jLattice_eq_c₄_pow_three_div_Δ, WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ',
    div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val]

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.WeierstrassCurve.Affine AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.ModularCurve in
theorem solution
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : Squarefree N) (data : ModularCurve.ModularPolynomialData N)
    (D : IsogenyEndDatum W.toAffine) (hdeg : finrankAlong K D.ι = N) :
    Polynomial.aeval W.j (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X) = 0 := by
  classical

  obtain ⟨K₀, hK₀c, E₀, hE₀e, hE₀map, ι₀, hι₀, hfin₀, hrk₀⟩ :=
    WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq W D.ι D.hι D.hfin
  haveI := hE₀e
  haveI : Countable K₀ := hK₀c
  haveI : CharZero (AlgebraicClosure K₀) :=
    charZero_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective

  obtain ⟨σ⟩ := kw_nonempty_ringHom_algebraicClosure_complex (↥K₀)
  letI : Algebra (AlgebraicClosure K₀) ℂ := σ.toAlgebra
  letI : Algebra (↥K₀) ℂ := (σ.comp (algebraMap (↥K₀) (AlgebraicClosure K₀))).toAlgebra
  haveI : IsScalarTower (↥K₀) (AlgebraicClosure K₀) ℂ := IsScalarTower.of_algebraMap_eq' rfl

  obtain ⟨ι₁, hι₁, hfin₁, hrk₁⟩ :=
    WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq E₀
      (AlgebraicClosure K₀) ℂ ι₀ hι₀ hfin₀
  have hN₁ : finrankAlong ℂ ι₁ = N := hrk₁.trans (hrk₀.trans hdeg)

  have hjK : W.j = algebraMap (↥K₀) K E₀.j := by
    subst hE₀map
    exact E₀.map_j (algebraMap (↥K₀) K)
  haveI hE1inst : (E₀.baseChange ℂ).IsElliptic :=
    inferInstanceAs (E₀.map (algebraMap (↥K₀) ℂ)).IsElliptic
  have hjC : (E₀.baseChange ℂ).j = algebraMap (↥K₀) ℂ E₀.j := E₀.map_j (algebraMap (↥K₀) ℂ)

  set d := data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X with hd
  suffices hℂ : Polynomial.aeval (E₀.baseChange ℂ).j d = 0 by

    have h0 : Polynomial.aeval E₀.j d = 0 := by
      apply (algebraMap (↥K₀) ℂ).injective
      rw [map_zero, ← Polynomial.aeval_algebraMap_apply, ← hjC]
      exact hℂ
    rw [hjK, Polynomial.aeval_algebraMap_apply, h0, map_zero]
  generalize hE1 : E₀.baseChange ℂ = E₁ at ι₁ hι₁ hfin₁ hN₁ hE1inst
  obtain ⟨L, C, hC⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq E₁
  subst hC

  have hL : L.DiscriminantNeZero := PeriodPair.discriminant_ne_zero L
  haveI hLe : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hL.weierstrassCurve_Δ_ne_zero⟩
  haveI : IsDedekindDomain L.weierstrassCurve.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain L.weierstrassCurve
  haveI : HasPrincipalDivisors ℂ L.weierstrassCurve.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g, hgc, hga⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := L.weierstrassCurve.toAffine)
  letI := g
  haveI := hgc
  haveI := hga

  obtain ⟨eE⟩ := WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange L.weierstrassCurve C
  let ι₂ := kw_fdn2_qephod_hend21_conjSeam eE eE ι₁
  have hι₂ : ι₂.toRingHom.IsIntegral := kw_fdn2_qephod_hend21_conjSeam_isIntegral eE eE ι₁ hι₁
  have hfin₂ : FiniteAlong ℂ ι₂ := kw_fdn2_qephod_hend21_conjSeam_finiteAlong eE eE ι₁ hfin₁
  have hrk₂ : finrankAlong ℂ ι₂ = N := (kw_fdn2_qephod_hend21_finrankAlong_conj eE eE ι₁).trans hN₁

  have hN₂ : NormFormulaAlong ℂ ι₂ hfin₂ := normFormulaAlong_of_elliptic ι₂ hfin₂
  have hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N :=
    (WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong _ _ ι₂ hι₂ hfin₂ hN₂).trans hrk₂
  have hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker :=
    IsAddCyclic.of_squarefree_natCard (hcard.symm ▸ hN)

  obtain ⟨β, hsub, hidx, hcq⟩ :=
    PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
      L L ι₂ hι₂ hfin₂ hN₂ N hcyc hcard
  have hroot := ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic N data L (L.scale β)
    hsub hidx hcq
  rw [PeriodPair.jLattice_scale] at hroot

  rw [WeierstrassCurve.variableChange_j, s13_j_weierstrassCurve_eq_jLattice, s13_aeval_diag_eq_eval_map]
  exact hroot

end
end S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq (solution)

-- Prove2me | solution 1 for WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/df966f14-8421-56b3-8b4d-c304d5f46f47

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong SeparableAlong Place.deg_restrict_mul_inertiaDeg Place.mem_fiber Place HasPrincipalDivisors Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor Place.valuationSubringAlgebra Place.sum_ramificationIndex_mul_inertiaDeg"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndex restrict inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ext deg ord exists_unit_mul_zpow toValuationSubring mk center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver sum_ramificationIndex_mul_inertiaDeg ramificationIndex_eq_ramificationIdx_fiberCenter"
p2m_open "AlgebraicCurve.Place~mem_of_ord_nonneg AlgebraicCurve~Place.mem_of_ord_nonneg"

open IsDedekindDomain WithZero IsLocalRing

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end SinglePlace

end AlgebraicCurve.Place

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong SeparableAlong Place.deg_restrict_mul_inertiaDeg Place.mem_fiber Place HasPrincipalDivisors Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor Place.valuationSubringAlgebra Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg"

section Producer

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def IntegralAt (v : Place K F) (q : Polynomial F) : Prop :=
  ∀ i, q.coeff i ∈ v.toValuationSubring

theorem mem_lifts_of_integralAt {v : Place K F} {q : Polynomial F}
    (hq : IntegralAt v q) :
    q ∈ Polynomial.lifts (algebraMap v.toValuationSubring F) :=
  (Polynomial.lifts_iff_coeff_lifts q).mpr fun n => ⟨⟨q.coeff n, hq n⟩, rfl⟩

end Producer

section PolarLocus

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

theorem finite_setOf_ord_ne_zero_of_hasPrincipalDivisors {f : F} (hf : f ≠ 0) :
    {v : Place K F | v.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine D.support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.mpr ?_
  rw [hD v]
  exact hv

theorem finite_setOf_notMem_toValuationSubring (f : F) :
    {v : Place K F | f ∉ v.toValuationSubring}.Finite := by
  rcases eq_or_ne f 0 with rfl | hf
  · refine Set.finite_empty.subset fun v hv => ?_
    exact absurd (v.toValuationSubring.zero_mem) hv
  · refine (finite_setOf_ord_ne_zero_of_hasPrincipalDivisors (K := K) hf).subset
      fun v hv => ?_
    intro h0
    exact hv (v.mem_of_ord_nonneg hf h0.ge)

end PolarLocus

end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong SeparableAlong Place.deg_restrict_mul_inertiaDeg Place.mem_fiber Place HasPrincipalDivisors Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor Place.valuationSubringAlgebra Place.sum_ramificationIndex_mul_inertiaDeg"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndex restrict inertiaDeg deg_restrict_mul_inertiaDeg fiber mem_fiber ext deg ord exists_unit_mul_zpow toValuationSubring mk center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver sum_ramificationIndex_mul_inertiaDeg ramificationIndex_eq_ramificationIdx_fiberCenter"
p2m_open "AlgebraicCurve.Place~mem_of_ord_nonneg AlgebraicCurve~Place.mem_of_ord_nonneg"

open Polynomial IsDedekindDomain

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

variable {v : Place K F} {w : Place K F'}

theorem ord_deriv_pos_of_ramificationIndex_ne_one
    (hw : w.restrict F = v) (θ : F')
    (hgen : IntermediateField.adjoin F {θ} = ⊤)
    (hθint : _root_.IsIntegral v.toValuationSubring θ)
    (hram : w.ramificationIndex F ≠ 1) :
    0 < w.ord (aeval θ (derivative (minpoly F θ))) := by

  obtain ⟨c, rfl⟩ : ∃ c : integralClosureAt F' v,
      algebraMap (integralClosureAt F' v) F' c = θ := ⟨⟨θ, hθint⟩, rfl⟩
  have hAc : _root_.IsIntegral v.toValuationSubring c := Algebra.IsIntegral.isIntegral c

  have hadjF : Algebra.adjoin F {algebraMap (integralClosureAt F' v) F' c} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hgen, IntermediateField.top_toSubalgebra]

  have hmem : aeval c (derivative (minpoly v.toValuationSubring c))
      ∈ differentIdeal v.toValuationSubring (integralClosureAt F' v) :=
    aeval_derivative_mem_differentIdeal (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v) c hadjF

  have himg : aeval (algebraMap (integralClosureAt F' v) F' c)
        (derivative (minpoly F (algebraMap (integralClosureAt F' v) F' c)))
      = algebraMap (integralClosureAt F' v) F'
          (aeval c (derivative (minpoly v.toValuationSubring c))) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions F F' hAc, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply]

  have hg0 : aeval (algebraMap (integralClosureAt F' v) F' c)
      (derivative (minpoly F (algebraMap (integralClosureAt F' v) F' c))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F _).aeval_derivative_ne_zero (minpoly.aeval F _)
  have hc0 : aeval c (derivative (minpoly v.toValuationSubring c)) ≠ 0 := by
    intro h; exact hg0 (by rw [himg, h, _root_.map_zero])

  haveI : FaithfulSMul v.toValuationSubring (integralClosureAt F' v) :=
    (faithfulSMul_iff_algebraMap_injective v.toValuationSubring (integralClosureAt F' v)).mpr
      (algebraMap_integralClosureAt_injective v)
  letI : Algebra (FractionRing v.toValuationSubring) (FractionRing (integralClosureAt F' v)) :=
    FractionRing.liftAlgebra v.toValuationSubring (FractionRing (integralClosureAt F' v))
  haveI : IsScalarTower v.toValuationSubring (FractionRing v.toValuationSubring)
      (FractionRing (integralClosureAt F' v)) :=
    FractionRing.isScalarTower_liftAlgebra (R := v.toValuationSubring)
      (K := FractionRing (integralClosureAt F' v))
  haveI : Algebra.IsSeparable (FractionRing v.toValuationSubring)
      (FractionRing (integralClosureAt F' v)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv v.toValuationSubring F).symm.toRingEquiv
      (FractionRing.algEquiv (integralClosureAt F' v) F').symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv v.toValuationSubring F).symm
      (FractionRing.algEquiv (integralClosureAt F' v) F').symm _
  haveI := (fiberCenter F' v hw).isPrime
  have hdvd : (fiberCenter F' v hw).asIdeal
      ∣ differentIdeal v.toValuationSubring (integralClosureAt F' v) := by
    by_contra hnd
    haveI : Algebra.IsUnramifiedAt v.toValuationSubring (fiberCenter F' v hw).asIdeal :=
      not_dvd_differentIdeal_iff.mp hnd
    have he1 : Ideal.ramificationIdx'
        ((fiberCenter F' v hw).asIdeal.under v.toValuationSubring)
        (fiberCenter F' v hw).asIdeal = 1 :=
      (Ideal.ramificationIdx'_eq_ramificationIdx _ _
          (Ideal.under_ne_bot (A := v.toValuationSubring) (fiberCenter F' v hw).ne_bot)).trans
        Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    exact hram <| by
      rw [ramificationIndex_eq_ramificationIdx_fiberCenter (v := v) hw,
        (fiberCenter_liesOver hw).over, he1]

  have hmem2 : aeval c (derivative (minpoly v.toValuationSubring c))
      ∈ (fiberCenter F' v hw).asIdeal := Ideal.le_of_dvd hdvd hmem
  rw [himg]
  exact (mem_fiberCenter_iff_ord_pos hw hc0).mp hmem2

end AlgebraicCurve.Place

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk IsIntegral minimal Affine.deg_eq_one card_torsionBy_eq_sq_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map FunctionField Point polynomial pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply IsogenyEndDatum GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply hasPrincipalDivisors_functionField pointMapOfPushforward_surjective"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.AlgebraicCurve"

section Gate

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable {W : Affine F} [GenusOnePlaceGate W]

theorem placeOfPoint_injective : Function.Injective (placeOfPoint (W := W)) :=
  (pointEquivPlace (W := W)).injective

variable (W)

def placeOfPointEquiv : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)

@[scoped simp] theorem placeOfPointEquiv_symm_placeOfPoint (P : W.Point) :
    (placeOfPointEquiv W).symm (placeOfPoint P) = P :=
  (placeOfPointEquiv W).symm_apply_apply P

theorem placeOfPoint_placeOfPointEquiv_symm (w : AlgebraicCurve.Place F W.FunctionField) :
    placeOfPoint ((placeOfPointEquiv W).symm w) = w :=
  (placeOfPointEquiv W).apply_symm_apply w

end Gate

section GeneralW

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic]

theorem kw_point_infinite : Infinite W.Point := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  haveI : Finite W.Point := hfinite
  set N : ℕ := Nat.card W.Point with hN
  have hNpos : 0 < N := Nat.card_pos
  have htop : ∀ k : ℕ, N ∣ k → Submodule.torsionBy ℤ W.Point (k : ℤ) = ⊤ := by
    rintro k ⟨c, rfl⟩
    refine eq_top_iff.mpr fun P _ => ?_
    rw [Submodule.mem_torsionBy_iff]
    have hP : (N : ℤ) • P = 0 := by
      rw [natCast_zsmul, hN]; exact card_nsmul_eq_zero'
    rw [Nat.cast_mul, mul_comm, mul_smul, hP, smul_zero]
  have hcard : ∀ k : ℕ, N ∣ k → k ≠ 0 → N = k ^ 2 := by
    intro k hk hk0
    have h : Nat.card (Submodule.torsionBy ℤ W.Point (k : ℤ)) = k ^ 2 :=
      WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := k)
        (Nat.cast_ne_zero.mpr hk0) two_ne_zero
    rw [htop k hk] at h
    rwa [Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := W.Point)).toEquiv, ← hN] at h
  have h1 := hcard N dvd_rfl hNpos.ne'
  have h2 := hcard (2 * N) (dvd_mul_left N 2) (by omega)
  have h3 : N ^ 2 = (2 * N) ^ 2 := h1.symm.trans h2
  have h4 : N ^ 2 = 0 := by nlinarith
  exact hNpos.ne' (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4)

end GeneralW

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve"

namespace ModularCurve

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine Polynomial AlgebraicCurve~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.AlgebraicCurve"

universe u

attribute [local instance] Classical.propDecidable

def KwD5PointMapOfPushforwardKerCard : Prop :=
  ∀ (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hN : NormFormulaAlong K ι hfin),
    Nat.card ((pointMapOfPushforward ι hι hfin hN).ker) = finrankAlong K ι

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

theorem kw_fdn2_qephod_hend5_natCard_fiber_eq_finrank_of_unramified
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (hdegF : ∀ v : Place K F, v.deg = 1) (hdegF' : ∀ w : Place K F', w.deg = 1)
    (v : Place K F)
    (hv : letI := algebraAlong φ
      haveI := isScalarTower_along φ
      haveI := isIntegral_along φ hφ
      ∀ w : Place K F', w.restrict F = v → w.ramificationIndex F = 1) :
    Nat.card {w : Place K F' // w.restrictAlong φ hφ = v} = finrankAlong K φ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FiniteDimensional F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
    (K := K) (F := F) (F' := F') v

  have hcoll : ∀ w ∈ v.fiber F',
      (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) = 1 := by
    intro w hw
    have hf : w.inertiaDeg F = 1 := by
      have h := Place.deg_restrict_mul_inertiaDeg (F := F) w
      rw [hdegF, hdegF', one_mul] at h
      exact h
    rw [hv w (Place.mem_fiber.mp hw), hf, Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl hcoll, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hcard : (v.fiber F').card = finrankAlong K φ := by
    have h : ((v.fiber F').card : ℤ) = (finrankAlong K φ : ℤ) := hsum
    exact_mod_cast h
  rw [← hcard]
  refine Nat.card_congr ?_ |>.trans (Nat.card_eq_finsetCard _)
  exact {
    toFun := fun ⟨w, hw⟩ => ⟨w, Place.mem_fiber.mpr hw⟩
    invFun := fun ⟨w, hw⟩ => ⟨w, Place.mem_fiber.mp hw⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end Generic
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine"

def KwD5ExistsUnramifiedBetweenCurves : Prop :=
  ∀ (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (_hfin : FiniteAlong K ι),
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI := isIntegral_along ι hι
    ∃ v : Place K E'.FunctionField,
      ∀ w : Place K E.FunctionField,
        w.restrict E'.FunctionField = v → w.ramificationIndex E'.FunctionField = 1

def KwD5RestrictFiberEqKerPMOP : Prop :=
  ∀ (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hN : NormFormulaAlong K ι hfin)
    (v : Place K E'.FunctionField),
    Nat.card {w : Place K E.FunctionField // w.restrictAlong ι hι = v}
      = Nat.card (AddMonoidHom.ker (pointMapOfPushforward ι hι hfin hN))

theorem kw_fdn2_qephod_hend5_pmopKerCard_of_twoAtoms
    (hUnram : KwD5ExistsUnramifiedBetweenCurves.{u})
    (hFiberKer : KwD5RestrictFiberEqKerPMOP.{u}) :
    KwD5PointMapOfPushforwardKerCard.{u} := by
  intro K _ _ _ _ E E' _ _ _ _ _ _ ι hι hfin hN
  obtain ⟨v, hv⟩ := hUnram K E E' ι hι hfin
  haveI : HasPrincipalDivisors K E.FunctionField := hasPrincipalDivisors_functionField E
  have hsep : SeparableAlong K ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
    haveI : CharZero E'.FunctionField :=
      charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
    show Algebra.IsSeparable E'.FunctionField E.FunctionField
    infer_instance
  have h0 := kw_fdn2_qephod_hend5_natCard_fiber_eq_finrank_of_unramified ι hι hfin hsep
    (fun v' => WeierstrassCurve.Affine.deg_eq_one (W := E') v')
    (fun w => WeierstrassCurve.Affine.deg_eq_one (W := E) w)
    v hv
  have h2 := hFiberKer K E E' ι hι hfin hN v
  exact h2.symm.trans h0

theorem kw_fdn2_qephod_hend6_existsUnramifiedBetweenCurves_proved :
    KwD5ExistsUnramifiedBetweenCurves.{u} := by
  intro K _ _ _ _ E E' _ _ _ _ _ _ ι hι hfin
  classical

  letI := algebraAlong ι
  haveI := isScalarTower_along ι
  haveI := isIntegral_along ι hι
  haveI hfin' : Module.Finite E'.FunctionField E.FunctionField := hfin
  haveI hcz : CharZero E'.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
  haveI hsep : Algebra.IsSeparable E'.FunctionField E.FunctionField := inferInstance
  haveI hpdE : HasPrincipalDivisors K E.FunctionField := hasPrincipalDivisors_functionField E
  haveI hpdE' : HasPrincipalDivisors K E'.FunctionField := hasPrincipalDivisors_functionField E'

  obtain ⟨θ, hgen⟩ := Field.exists_primitive_element E'.FunctionField E.FunctionField
  have hpmon : (minpoly E'.FunctionField θ).Monic :=
    minpoly.monic (_root_.IsIntegral.of_finite E'.FunctionField θ)
  have hg0 : aeval θ (derivative (minpoly E'.FunctionField θ)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable E'.FunctionField θ).aeval_derivative_ne_zero
      (minpoly.aeval E'.FunctionField θ)

  let S₁ : Set (Place K E'.FunctionField) :=
    ⋃ i ∈ (minpoly E'.FunctionField θ).support,
      {v | (minpoly E'.FunctionField θ).coeff i ∉ v.toValuationSubring}
  let S₂ : Set (Place K E.FunctionField) :=
    {w | w.ord (aeval θ (derivative (minpoly E'.FunctionField θ))) ≠ 0}
  have hS₁fin : S₁.Finite :=
    Set.Finite.biUnion (minpoly E'.FunctionField θ).support.finite_toSet fun i _ =>
      finite_setOf_notMem_toValuationSubring (K := K) ((minpoly E'.FunctionField θ).coeff i)
  have hS₂fin : S₂.Finite :=
    finite_setOf_ord_ne_zero_of_hasPrincipalDivisors (K := K) hg0
  have hSfin : (S₁ ∪ (fun w => w.restrict E'.FunctionField) '' S₂).Finite :=
    hS₁fin.union (hS₂fin.image _)

  haveI : Infinite (Place K E'.FunctionField) :=
    (placeOfPointEquiv E').symm.infinite_iff.mpr (kw_point_infinite (W := E'))
  obtain ⟨v, hv⟩ := hSfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hv
  obtain ⟨hvS₁, hvS₂⟩ := hv

  refine ⟨v, fun w hw => ?_⟩
  by_contra hram

  have hcoeff : ∀ i, (minpoly E'.FunctionField θ).coeff i ∈ v.toValuationSubring := by
    intro i
    by_contra hni
    have hci : (minpoly E'.FunctionField θ).coeff i ≠ 0 :=
      fun h => hni (h ▸ v.toValuationSubring.zero_mem)
    exact hvS₁ (Set.mem_biUnion (Finset.mem_coe.mpr (mem_support_iff.mpr hci)) hni)
  obtain ⟨Q, hQmap, -, hQmon⟩ :=
    lifts_and_degree_eq_and_monic (mem_lifts_of_integralAt (fun i => hcoeff i)) hpmon
  have hθint : @_root_.IsIntegral v.toValuationSubring E.FunctionField _ _
      (Place.valuationSubringAlgebra E.FunctionField v) θ := by
    refine ⟨Q, hQmon, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.eval₂_map, hQmap]
    exact minpoly.aeval E'.FunctionField θ

  have hpos := Place.ord_deriv_pos_of_ramificationIndex_ne_one
    (K := K) (F := E'.FunctionField) (F' := E.FunctionField)
    (v := v) (w := w) hw θ hgen hθint hram

  exact hvS₂ ⟨w, hpos.ne', hw⟩

section GeomMorphBC

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
  [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hN : NormFormulaAlong K ι hfin)

def kw_fdn2_qephod_hend7_geomMorphBC : E.Point → E'.Point :=
  fun P => (placeOfPointEquiv E').symm ((placeOfPoint P).restrictAlong ι hι)

local notation "gBC" => kw_fdn2_qephod_hend7_geomMorphBC ι hι

theorem kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC (P : E.Point) :
    (placeOfPoint P).restrictAlong ι hι = placeOfPoint (gBC P) :=
  (placeOfPoint_placeOfPointEquiv_symm E' _).symm

theorem kw_fdn2_qephod_hend7_pushforwardDegZero_pointDivisor_geomMorphBC (P : E.Point) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P)
      = pointDivisor (gBC P) - pointDivisor (gBC 0) := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq ι hι, pushforwardAlong_single_eq ι hι,
    kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι P,
    kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι 0]
  push_cast
  rw [coe_pointDivisor, coe_pointDivisor, sub_sub_sub_cancel_right]

include hfin in

theorem kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub (P : E.Point) :
    Pic0.pushforwardAlongHom ι hι hfin hN
        (pointClass P)
      = pointClass (gBC P) - pointClass (gBC 0) := by
  show Pic0.pushforwardAlongHom ι hι hfin _ (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor (gBC P)) - Pic0.mk (pointDivisor (gBC 0))
  rw [Pic0.pushforwardAlongHom_mk,
    kw_fdn2_qephod_hend7_pushforwardDegZero_pointDivisor_geomMorphBC ι hι P]
  rfl

include hfin in

theorem kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (P : E.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = gBC P - gBC 0 := by
  rw [pointMapOfPushforward_apply,
    kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub ι hι hfin hN P, map_sub,
    genusOnePic0Equiv_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass,
    pic0ToPoint_pointClass]

def kw_fdn2_qephod_hend7_restrictAlong_fiber_equiv_pmop_fiber
    (v : Place K E'.FunctionField) :
    {w : Place K E.FunctionField // w.restrictAlong ι hι = v}
      ≃ {P : E.Point //
          pointMapOfPushforward ι hι hfin hN P
            = (placeOfPointEquiv E').symm v - gBC 0} where
  toFun := fun ⟨w, hw⟩ => ⟨(placeOfPointEquiv E).symm w, by
    rw [kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι hι hfin hN, sub_left_inj]
    refine placeOfPoint_injective ?_
    rw [← kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι,
      placeOfPoint_placeOfPointEquiv_symm, hw, placeOfPoint_placeOfPointEquiv_symm]⟩
  invFun := fun ⟨P, hP⟩ => ⟨placeOfPoint P, by
    rw [kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι P,
      ← placeOfPoint_placeOfPointEquiv_symm E' v]
    congr 1
    have h : gBC P - gBC 0
        = (placeOfPointEquiv E').symm v - gBC 0 :=
      (kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι hι hfin hN P).symm.trans hP
    exact sub_left_injective h⟩
  left_inv := fun ⟨w, _⟩ => Subtype.ext (placeOfPoint_placeOfPointEquiv_symm E w)
  right_inv := fun ⟨P, _⟩ => Subtype.ext (placeOfPointEquiv_symm_placeOfPoint E P)

def kw_fdn2_qephod_hend7_pmop_fiber_equiv_ker (R : E'.Point) :
    {P : E.Point //
        pointMapOfPushforward ι hι hfin hN P = R}
      ≃ (AddMonoidHom.ker
          (pointMapOfPushforward ι hι hfin hN)) :=
  let φ := pointMapOfPushforward ι hι hfin hN
  let hsurj : Function.Surjective φ :=
    pointMapOfPushforward_surjective E E' ι hι hfin hN
  let P₀ : E.Point := (hsurj R).choose
  have hP₀ : φ P₀ = R := (hsurj R).choose_spec
  { toFun := fun ⟨P, hP⟩ => ⟨P - P₀, by
      show φ (P - P₀) = 0
      rw [map_sub, hP, hP₀, sub_self]⟩
    invFun := fun ⟨Q, hQ⟩ => ⟨Q + P₀, by
      show φ (Q + P₀) = R
      have hQ' : φ Q = 0 := hQ
      rw [map_add, hQ', zero_add, hP₀]⟩
    left_inv := fun ⟨P, _⟩ => Subtype.ext (sub_add_cancel P P₀)
    right_inv := fun ⟨Q, _⟩ => Subtype.ext (add_sub_cancel_right Q P₀) }

end GeomMorphBC
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine"

theorem kw_fdn2_qephod_hend7_restrictFiberEqKerPMOP_proved :
    KwD5RestrictFiberEqKerPMOP.{u} := by
  intro K _ _ _ _ E E' _ _ _ _ _ _ ι hι hfin hN v
  exact Nat.card_congr
    ((kw_fdn2_qephod_hend7_restrictAlong_fiber_equiv_pmop_fiber ι hι hfin hN v).trans
      (kw_fdn2_qephod_hend7_pmop_fiber_equiv_ker ι hι hfin hN _))

theorem kw_fdn2_qephod_hend7_pmopKerCard_proved :
    KwD5PointMapOfPushforwardKerCard.{u} :=
  kw_fdn2_qephod_hend5_pmopKerCard_of_twoAtoms
    kw_fdn2_qephod_hend6_existsUnramifiedBetweenCurves_proved
    kw_fdn2_qephod_hend7_restrictFiberEqKerPMOP_proved

end ModularCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine"

p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg" in open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.AlgebraicCurve in
universe u in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Nat.card (pointMapOfPushforward ι hι hfin hN).ker = finrankAlong F ι :=
  ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved F E E' ι hι hfin hN

end S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
end P2MW
export P2MW.S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong (solution)

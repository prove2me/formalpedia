-- Prove2me | solution 1 for WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a8b71afd-afb7-5df0-be34-30cd3f5422dd

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred
import Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
import Theorems.Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring
import Theorems.Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_AlgebraicCurve_finiteAlong_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply"
p2m_attr_erase "simp" "ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace ModularCurve

theorem cmm5_dp_natCard_ker_comp {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (AddMonoidHom.ker (g.comp f))
      = Nat.card (AddMonoidHom.ker g) * Nat.card (AddMonoidHom.ker f) := by

  have hmem : ∀ x : AddMonoidHom.ker (g.comp f),
      (f.domRestrict (AddMonoidHom.ker (g.comp f))) x ∈ AddMonoidHom.ker g := by
    intro x
    have hx := x.2
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_ker]
    exact hx

  have hle : AddMonoidHom.ker f ≤ AddMonoidHom.ker (g.comp f) := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx, map_zero]
  have hφker : Nat.card (AddMonoidHom.ker
        (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
          (AddMonoidHom.ker g) hmem))
      = Nat.card (AddMonoidHom.ker f) := by
    rw [AddMonoidHom.ker_codRestrict, AddMonoidHom.ker_domRestrict]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv

  have hφsurj : Function.Surjective
      (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
        (AddMonoidHom.ker g) hmem) := by
    intro y
    have hy : g (y : B) = 0 := by
      have h := y.2
      rwa [AddMonoidHom.mem_ker] at h
    obtain ⟨x, hx⟩ := hf (y : B)
    have hxK : x ∈ AddMonoidHom.ker (g.comp f) := by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx]
      exact hy
    exact ⟨⟨x, hxK⟩, Subtype.ext hx⟩
  calc Nat.card (AddMonoidHom.ker (g.comp f))
      = Nat.card (AddMonoidHom.ker (g.comp f) ⧸ AddMonoidHom.ker
            (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
              (AddMonoidHom.ker g) hmem))
          * Nat.card (AddMonoidHom.ker
            (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
              (AddMonoidHom.ker g) hmem)) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card (AddMonoidHom.ker g) * Nat.card (AddMonoidHom.ker f) := by
        rw [Nat.card_congr
          (QuotientAddGroup.quotientKerEquivOfSurjective _ hφsurj).toEquiv, hφker]

end ModularCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map exists_variableChange_of_j_eq IsIntegral toAffine Affine.Point j Affine.pointMapOfPushforward Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.Point.exists_zsmul_eq_of_isAlgClosed card_torsionBy_eq_sq_of_isAlgClosed nonempty_functionField_algEquiv_of_variableChange"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map FunctionField Point pointMapOfPushforward pointMapOfPushforward_apply IsogenyEndDatum IsogenyHomDatum IsogenyHomDatum.ofEndDatum GenusOnePlaceGate pointClass AbelTheorem genusOnePic0Equiv genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred natCard_ker_pointMapOfPushforward_eq_finrankAlong pointMapOfPushforward_surjective Point.exists_zsmul_eq_of_isAlgClosed IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve.Affine~pointHom WeierstrassCurve"

open AlgebraicCurve

scoped instance instHasPrincipalDivisorsFunctionField_a68c2 {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

section AutoNorm

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) : NormFormulaAlong F ι hfin := by
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

section Torsion

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic]

theorem charZero_addMonoidEnd_point : CharZero (AddMonoid.End W.Point) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  have htop : ∀ k : ℕ, n ∣ k → Submodule.torsionBy ℤ W.Point (k : ℤ) = ⊤ := by
    rintro k ⟨c, rfl⟩
    refine eq_top_iff.mpr fun P _ => ?_
    rw [Submodule.mem_torsionBy_iff]
    have hP : (n : ℤ) • P = 0 := by
      have h := DFunLike.congr_fun hn P
      rw [AddMonoid.End.natCast_apply] at h
      rw [natCast_zsmul]; exact h
    rw [Nat.cast_mul, mul_comm, mul_smul, hP, smul_zero]
  have hcard : ∀ k : ℕ, n ∣ k → k ≠ 0 → Nat.card W.Point = k ^ 2 := by
    intro k hk hk0
    have h : Nat.card (Submodule.torsionBy ℤ W.Point (k : ℤ)) = k ^ 2 :=
      WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := k)
        (Nat.cast_ne_zero.mpr hk0) two_ne_zero
    rw [htop k hk] at h
    rwa [Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := W.Point)).toEquiv] at h
  have h1 := hcard n dvd_rfl hn0
  have h2 := hcard (2 * n) (dvd_mul_left n 2) (by omega)
  have h3 : n ^ 2 = (2 * n) ^ 2 := h1.symm.trans h2
  have h4 : 3 * n ^ 2 = 0 := by nlinarith
  have h5 : n = 0 := by
    have : n ^ 2 = 0 := by omega
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact hn0 h5

theorem intCast_addMonoidEnd_point_injective :
    Function.Injective (Int.cast : ℤ → AddMonoid.End W.Point) :=
  haveI := charZero_addMonoidEnd_point W
  Int.cast_injective

variable {W} in

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

variable {W} in

theorem kw_nat_card_ker_of_zsmul {f : W.Point →+ W.Point} {N : ℤ}
    (hN : N ≠ 0) (hf : ∀ P, f P = N • P) : Nat.card f.ker = N.natAbs ^ 2 := by
  have hsets : ∀ P : W.Point,
      P ∈ f.ker ↔ P ∈ Submodule.torsionBy ℤ W.Point (N.natAbs : ℤ) := by
    intro P
    rw [AddMonoidHom.mem_ker, hf, Submodule.mem_torsionBy_iff]
    constructor
    · intro hP
      rcases Int.natAbs_eq N with h | h
      · rwa [h] at hP
      · rwa [h, neg_zsmul, neg_eq_zero] at hP
    · intro hP
      rcases Int.natAbs_eq N with h | h
      · rw [h]; exact hP
      · rw [h, neg_zsmul, neg_eq_zero]; exact hP
  rw [Nat.card_congr (Equiv.subtypeEquivRight hsets)]
  exact WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := N.natAbs)
    (Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN)) two_ne_zero

variable {W} in

theorem kw_eq_zero_of_zsmul_eq_zero {N : ℤ} (hN : N ≠ 0) {G : Type*} [AddCommGroup G]
    (δ : W.Point →+ G) (hδ : ∀ P, N • δ P = 0) : δ = 0 := by
  refine AddMonoidHom.ext fun P => ?_
  obtain ⟨R, hR⟩ : ∃ R : W.Point, N • R = P :=
    WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed W hN P
  rw [← hR, map_zsmul]; exact hδ R

end Torsion

section Functoriality

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {A B C : Affine F}
  [A.IsElliptic] [GenusOnePlaceGate A] [AbelTheorem A]
  [B.IsElliptic] [GenusOnePlaceGate B] [AbelTheorem B]
  [C.IsElliptic] [GenusOnePlaceGate C] [AbelTheorem C]

theorem Pic0_pushforwardAlongHom_comp
    (f : B.FunctionField →ₐ[F] A.FunctionField) (hf : f.toRingHom.IsIntegral)
    (hfinf : FiniteAlong F f) (hNf : NormFormulaAlong F f hfinf)
    (g : C.FunctionField →ₐ[F] B.FunctionField) (hg : g.toRingHom.IsIntegral)
    (hfing : FiniteAlong F g) (hNg : NormFormulaAlong F g hfing)
    (hfg : (f.comp g).toRingHom.IsIntegral) (hfinfg : FiniteAlong F (f.comp g))
    (hNfg : NormFormulaAlong F (f.comp g) hfinfg)
    (x : Pic0 F A.FunctionField) :
    Pic0.pushforwardAlongHom g hg hfing hNg (Pic0.pushforwardAlongHom f hf hfinf hNf x)
      = Pic0.pushforwardAlongHom (f.comp g) hfg hfinfg hNfg x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  congr 1
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pushforwardAlongDegZero,
    Pic0.coe_pushforwardAlongDegZero]
  exact Divisor.pushforwardAlong_pushforwardAlong g f hg hf hfg (D : Divisor F A.FunctionField)

theorem pointMapOfPushforward_comp
    (f : B.FunctionField →ₐ[F] A.FunctionField) (hf : f.toRingHom.IsIntegral)
    (hfinf : FiniteAlong F f) (hNf : NormFormulaAlong F f hfinf)
    (g : C.FunctionField →ₐ[F] B.FunctionField) (hg : g.toRingHom.IsIntegral)
    (hfing : FiniteAlong F g) (hNg : NormFormulaAlong F g hfing)
    (hfg : (f.comp g).toRingHom.IsIntegral) (hfinfg : FiniteAlong F (f.comp g))
    (hNfg : NormFormulaAlong F (f.comp g) hfinfg) (P : A.Point) :
    pointMapOfPushforward (f.comp g) hfg hfinfg hNfg P
      = pointMapOfPushforward g hg hfing hNg (pointMapOfPushforward f hf hfinf hNf P) := by
  have key : ∀ x : Pic0 F B.FunctionField, pointClass (genusOnePic0Equiv B x) = x := fun x => by
    rw [← genusOnePic0Equiv_symm_apply, AddEquiv.symm_apply_apply]
  rw [pointMapOfPushforward_apply, pointMapOfPushforward_apply, pointMapOfPushforward_apply, key,
    Pic0_pushforwardAlongHom_comp f hf hfinf hNf g hg hfing hNg hfg hfinfg hNfg]

end Functoriality

section IsoInjective

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {A B : Affine F}
  [A.IsElliptic] [GenusOnePlaceGate A] [AbelTheorem A]
  [B.IsElliptic] [GenusOnePlaceGate B] [AbelTheorem B]

theorem finrankAlong_eq_one_of_bijective (τ : B.FunctionField →ₐ[F] A.FunctionField)
    (hτ : Function.Bijective τ) : finrankAlong F τ = 1 := by
  letI := algebraAlong τ
  let σ : B.FunctionField ≃+* A.FunctionField := RingEquiv.ofBijective τ hτ
  let e : A.FunctionField ≃ₗ[B.FunctionField] B.FunctionField :=
    { σ.symm.toAddEquiv with
      map_smul' := fun b x => by
        show σ.symm (b • x) = b * σ.symm x
        rw [Algebra.smul_def, map_mul]
        congr 1
        exact σ.symm_apply_apply b }
  show Module.finrank B.FunctionField A.FunctionField = 1
  rw [e.finrank_eq, Module.finrank_self]

theorem pointMapOfPushforward_injective_of_bijective
    (τ : B.FunctionField →ₐ[F] A.FunctionField) (hτ : τ.toRingHom.IsIntegral)
    (hfin : FiniteAlong F τ) (hN : NormFormulaAlong F τ hfin) (hbij : Function.Bijective τ) :
    Function.Injective (pointMapOfPushforward τ hτ hfin hN) := by
  have hcard : Nat.card (pointMapOfPushforward τ hτ hfin hN).ker = 1 := by
    rw [natCard_ker_pointMapOfPushforward_eq_finrankAlong A B τ hτ hfin hN,
      finrankAlong_eq_one_of_bijective τ hbij]
  haveI : Finite (pointMapOfPushforward τ hτ hfin hN).ker :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact one_ne_zero)
  have hbot : (pointMapOfPushforward τ hτ hfin hN).ker = ⊥ :=
    AddSubgroup.eq_bot_of_card_eq _ hcard
  exact (AddMonoidHom.ker_eq_bot_iff _).mp hbot

end IsoInjective

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map exists_variableChange_of_j_eq IsIntegral toAffine Affine.Point j Affine.pointMapOfPushforward Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.Point.exists_zsmul_eq_of_isAlgClosed card_torsionBy_eq_sq_of_isAlgClosed nonempty_functionField_algEquiv_of_variableChange"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map FunctionField Point pointMapOfPushforward pointMapOfPushforward_apply IsogenyEndDatum IsogenyHomDatum IsogenyHomDatum.ofEndDatum GenusOnePlaceGate pointClass AbelTheorem genusOnePic0Equiv genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred natCard_ker_pointMapOfPushforward_eq_finrankAlong pointMapOfPushforward_surjective Point.exists_zsmul_eq_of_isAlgClosed IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve.Affine~pointHom WeierstrassCurve"

open AlgebraicCurve

universe u

attribute [local instance] Classical.propDecidable

theorem ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul_a68
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
    [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point,
      D.pointEnd (hNs D) P = m • P)
    (V V' : WeierstrassCurve F) [V.IsElliptic] [V'.IsElliptic]
    [GenusOnePlaceGate V.toAffine] [AbelTheorem V.toAffine]
    [GenusOnePlaceGate V'.toAffine] [AbelTheorem V'.toAffine]
    (ι : V.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)
    (ι' : V'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι' : ι'.toRingHom.IsIntegral) (hfin' : FiniteAlong F ι') (hN' : NormFormulaAlong F ι' hfin')
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker
      = Nat.card (pointMapOfPushforward ι' hι' hfin' hN').ker)
    (hj : V.j = V'.j) :
    (pointMapOfPushforward ι hι hfin hN).ker = (pointMapOfPushforward ι' hι' hfin' hN').ker := by
  classical

  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq V V' hj
  obtain ⟨σ⟩ : Nonempty (V.toAffine.FunctionField ≃ₐ[F] V'.toAffine.FunctionField) :=
    hC ▸ WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange V C

  set τ : V'.toAffine.FunctionField →ₐ[F] V.toAffine.FunctionField := σ.symm.toAlgHom with hτ_def
  have hτbij : Function.Bijective τ := σ.symm.bijective
  have hτint : τ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ hτbij.2
  have hτfin : FiniteAlong F τ := finiteAlong_of_surjective τ hτbij.2
  have hNτ : NormFormulaAlong F τ hτfin := normFormulaAlong_of_elliptic τ hτfin

  have hιτint : (ι.comp τ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hτint hι
  have hιτfin : FiniteAlong F (ι.comp τ) := finiteAlong_comp τ ι hτfin hfin
  have hNιτ : NormFormulaAlong F (ι.comp τ) hιτfin := normFormulaAlong_of_elliptic _ hιτfin
  set φ := pointMapOfPushforward ι hι hfin hN with hφ_def
  set φ' := pointMapOfPushforward ι' hι' hfin' hN' with hφ'_def
  set β := pointMapOfPushforward (ι.comp τ) hιτint hιτfin hNιτ with hβ_def
  have hβ_comp : ∀ P, β P = pointMapOfPushforward τ hτint hτfin hNτ (φ P) := fun P =>
    pointMapOfPushforward_comp ι hι hfin hN τ hτint hτfin hNτ hιτint hιτfin hNιτ P
  have hτinj := pointMapOfPushforward_injective_of_bijective τ hτint hτfin hNτ hτbij
  have hkerβ : β.ker = φ.ker := by
    refine AddSubgroup.ext fun P => ?_
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hβ_comp]
    refine ⟨fun h => hτinj (h.trans (map_zero _).symm), fun h => ?_⟩
    rw [h, map_zero]

  have hβs : Function.Surjective β :=
    pointMapOfPushforward_surjective W.toAffine _ (ι.comp τ) hιτint hιτfin hNιτ
  have hφ's : Function.Surjective φ' :=
    pointMapOfPushforward_surjective W.toAffine _ ι' hι' hfin' hN'

  set d : ℕ := Nat.card φ'.ker with hd_def
  have hdpos : 0 < d := by
    rw [hd_def, hφ'_def, natCard_ker_pointMapOfPushforward_eq_finrankAlong W.toAffine V'.toAffine
      ι' hι' hfin' hN']
    letI := algebraAlong ι'
    haveI : Module.Finite V'.toAffine.FunctionField W.toAffine.FunctionField := hfin'
    show 0 < Module.finrank V'.toAffine.FunctionField W.toAffine.FunctionField
    exact Module.finrank_pos
  have hd0 : d ≠ 0 := hdpos.ne'
  haveI hfinker : Finite φ'.ker := Nat.finite_of_card_ne_zero (hd_def ▸ hd0)

  have hNne : ((d : ℤ) : AddMonoid.End W.toAffine.Point) ≠ 0 := by
    intro h
    have := intCast_addMonoidEnd_point_injective W.toAffine (h.trans Int.cast_zero.symm)
    omega
  obtain ⟨M, hM⟩ := IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hNs
    ((d : ℤ) : AddMonoid.End W.toAffine.Point) (intCast_mem _ _) hNne
  have hMapp : ∀ P, M.pointEnd (hNs M) P = (d : ℤ) • P := fun P => by
    rw [hM, AddMonoid.End.intCast_apply]

  let φ'D : IsogenyHomDatum W.toAffine V'.toAffine := ⟨ι', hι', hfin'⟩
  have hmem_of_ker : ∀ P, φ' P = 0 → (d : ℤ) • P = 0 := by
    intro P hP
    have hx : Nat.card φ'.ker • (⟨P, (AddMonoidHom.mem_ker).mpr hP⟩ : φ'.ker) = 0 :=
      card_nsmul_eq_zero'
    have hx' := congrArg Subtype.val hx
    simp only [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero] at hx'
    rw [natCast_zsmul]
    exact hx'
  obtain ⟨χ, hNχ, hχ⟩ := IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred φ'D hN'
    (IsogenyHomDatum.ofEndDatum M) (hNs M) (fun P hP => by
      show M.pointEnd (hNs M) P = 0
      rw [hMapp]; exact hmem_of_ker P hP)
  set ψ' := χ.pointHom hNχ with hψ'_def
  have hdual₁ : ∀ P, ψ' (φ' P) = (d : ℤ) • P := fun P => by
    have h := hχ P
    rw [← hMapp P]; exact h
  have hdual₂ : ∀ S, φ' (ψ' S) = (d : ℤ) • S := fun S => by
    obtain ⟨P, rfl⟩ := hφ's S
    rw [hdual₁, map_zsmul]

  have hDint : ((ι.comp τ).comp χ.ι).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ χ.hι hιτint
  let D : IsogenyEndDatum W.toAffine :=
    ⟨(ι.comp τ).comp χ.ι, hDint, finiteAlong_comp χ.ι (ι.comp τ) χ.hfin hιτfin⟩
  have hD : ∀ P, D.pointEnd (hNs D) P = ψ' (β P) := fun P =>
    pointMapOfPushforward_comp (ι.comp τ) hιτint hιτfin hNιτ χ.ι χ.hι χ.hfin hNχ
      hDint D.hfin (hNs D) P
  obtain ⟨m, hm⟩ := hEnd D
  set θ := ψ'.comp β with hθ_def
  have hθm : ∀ P, θ P = m • P := fun P => by
    show ψ' (β P) = m • P
    rw [← hD P]; exact hm P

  have hkerψ' : Nat.card ψ'.ker = d := by
    have hcomp : Nat.card (ψ'.comp φ').ker = d ^ 2 := by
      have h := kw_nat_card_ker_of_zsmul (W := W.toAffine) (f := ψ'.comp φ')
        (N := (d : ℤ)) (by exact_mod_cast hd0) (fun P => hdual₁ P)
      rw [Int.natAbs_natCast] at h; exact h
    have hsplit := ModularCurve.cmm5_dp_natCard_ker_comp φ' ψ' hφ's
    rw [hcomp, ← hd_def, sq] at hsplit
    exact (Nat.eq_of_mul_eq_mul_right hdpos hsplit).symm

  have hkerθ : Nat.card θ.ker = d ^ 2 := by
    have hsplit := ModularCurve.cmm5_dp_natCard_ker_comp β ψ' hβs
    rw [hkerβ, hcard, hkerψ'] at hsplit
    rw [hθ_def, hsplit]; ring
  have hmne : m ≠ 0 := by
    intro h0
    have hall : ∀ P, θ P = 0 := fun P => by rw [hθm, h0, zero_zsmul]
    have htop : θ.ker = ⊤ :=
      AddSubgroup.ext fun P => ⟨fun _ => trivial, fun _ => AddMonoidHom.mem_ker.mpr (hall P)⟩
    rw [htop] at hkerθ
    haveI : Infinite W.toAffine.Point := kw_point_infinite
    simp only [AddSubgroup.card_top, Nat.card_eq_zero_of_infinite] at hkerθ
    exact absurd hkerθ.symm (by positivity)
  have hm_abs : m.natAbs = d := by
    have hcard' := kw_nat_card_ker_of_zsmul (W := W.toAffine) hmne hθm
    rw [hkerθ, sq, sq] at hcard'
    exact (Nat.mul_self_inj).mp hcard'.symm

  have hkey : ∀ P, (d : ℤ) • β P = m • φ' P := fun P => by
    have h1 : φ' (ψ' (β P)) = (d : ℤ) • β P := hdual₂ (β P)
    have h2 : φ' (θ P) = m • φ' P := by rw [hθm, map_zsmul]
    rw [← h1]; exact h2

  have hmcases : m = (d : ℤ) ∨ m = -(d : ℤ) := by
    rcases Int.natAbs_eq m with h | h <;> [left; right] <;> omega
  have hNz : (d : ℤ) ≠ 0 := by exact_mod_cast hd0
  have hkerβ' : β.ker = φ'.ker := by
    rcases hmcases with hm' | hm'
    · have hδ : β - φ' = 0 :=
        kw_eq_zero_of_zsmul_eq_zero (W := W.toAffine) hNz (β - φ') fun P => by
          rw [AddMonoidHom.sub_apply, smul_sub, hkey P, hm', sub_self]
      have heq : β = φ' := sub_eq_zero.mp hδ
      rw [heq]
    · have hδ : β + φ' = 0 :=
        kw_eq_zero_of_zsmul_eq_zero (W := W.toAffine) hNz (β + φ') fun P => by
          rw [AddMonoidHom.add_apply, smul_add, hkey P, hm', ← add_smul, neg_add_cancel,
            zero_smul]
      have heq : β = -φ' := eq_neg_iff_add_eq_zero.mpr hδ
      rw [heq]
      exact AddSubgroup.ext fun P => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.neg_apply, neg_eq_zero]
  exact hkerβ.symm.trans hkerβ'

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.WeierstrassCurve.Affine"

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    (hNs : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      AlgebraicCurve.NormFormulaAlong F D.ι D.hfin)
    (hEnd : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P)
    (V V' : WeierstrassCurve F) [V.IsElliptic] [V'.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem V.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V'.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem V'.toAffine]
    (ι : V.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι)
    (hN : AlgebraicCurve.NormFormulaAlong F ι hfin)
    (ι' : V'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι' : ι'.toRingHom.IsIntegral) (hfin' : AlgebraicCurve.FiniteAlong F ι')
    (hN' : AlgebraicCurve.NormFormulaAlong F ι' hfin')
    (hcard : Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker)
    (hj : V.j = V'.j) :
    (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker :=
  WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul_a68
    W hNs hEnd V V' ι hι hfin hN ι' hι' hfin' hN' hcard hj

end S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
end P2MW
export P2MW.S_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul (solution)

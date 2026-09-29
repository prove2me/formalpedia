-- Prove2me | solution 1 for WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/285a9016-3821-511c-ba86-36440e5c0200

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_GenusOnePic0
import Definitions.Def_PeriodPair_Uniformization
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
import Theorems.Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
import Theorems.Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
import Theorems.Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
import Theorems.Thm_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
import Theorems.Thm_Field_nonempty_ringHom_complex_of_countable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

noncomputable section

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ g₃ ω₂ G g₂ weierstrassCurve DiscriminantNeZero jLattice jLattice_eq_c₄_pow_three_div_Δ scale_indep scale exists_variableChange_smul_weierstrassCurve_eq exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient discriminant_ne_zero"
p2m_open "PeriodPair"
open Complex
variable (L : PeriodPair)
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
end PeriodPair
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.PeriodPair"

namespace F4Proof
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

section ConjHelpers
variable {K : Type*} [Field K]
variable {E E' F F' : WeierstrassCurve.Affine K}

def conjSeam
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    F'.FunctionField →ₐ[K] F.FunctionField :=
  (eE.symm.toAlgHom.comp ι).comp eE'.toAlgHom

theorem conjSeam_apply (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (x : F'.FunctionField) :
    conjSeam eE eE' ι x = eE.symm (ι (eE' x)) := rfl

theorem conjSeam_isIntegral
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) :
    (conjSeam eE eE' ι).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans eE'.toAlgHom.toRingHom (eE.symm.toAlgHom.comp ι).toRingHom
    (RingHom.isIntegral_of_surjective _ eE'.surjective)
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (RingHom.isIntegral_of_surjective _ eE.symm.surjective))

theorem conjSeam_finiteAlong
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    FiniteAlong K (conjSeam eE eE' ι) := by
  have hfin' : RingHom.Finite ι.toRingHom := hfin
  have h1 : RingHom.Finite eE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE'.surjective
  have h2 : RingHom.Finite eE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE.symm.surjective
  have hcomp : RingHom.Finite (conjSeam eE eE' ι).toRingHom :=
    RingHom.Finite.comp (g := (eE.symm.toAlgHom.comp ι).toRingHom)
      (RingHom.Finite.comp (g := eE.symm.toAlgHom.toRingHom) h2 hfin') h1
  exact hcomp

end ConjHelpers
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.PeriodPair"

section AutoNorm
variable {K : Type*} [Field K] [CharZero K]

theorem separableAlong_of_charZero {E E' : WeierstrassCurve.Affine K}
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    SeparableAlong K ι := by
  letI := algebraAlong ι
  haveI := isScalarTower_along ι
  haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
  haveI : CharZero E'.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
  show Algebra.IsSeparable E'.FunctionField E.FunctionField
  infer_instance

theorem normFormulaAlong_of_charZero {E E' : WeierstrassCurve.Affine K}
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    NormFormulaAlong K ι hfin := by
  haveI : HasPrincipalDivisors K E.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField E
  haveI : CharZero E'.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
  exact AlgebraicCurve.normFormulaAlong ι hfin (separableAlong_of_charZero ι hfin)

end AutoNorm
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.PeriodPair"

theorem map_eval_map_Φ {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N) (a b : R) :
    φ ((data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).eval b) =
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (φ a))).eval (φ b) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem isElliptic_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) [W.IsElliptic]
    (f : R →+* S) : (W.map f).IsElliptic :=
  ⟨by rw [WeierstrassCurve.map_Δ]; exact (W.isUnit_Δ).map f⟩

theorem j_eq_div {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j = W.c₄ ^ 3 / W.Δ := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', div_eq_inv_mul, Units.val_inv_eq_inv_val]

scoped instance instIsEllipticWeierstrassCurve (L : PeriodPair) : L.weierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (PeriodPair.discriminant_ne_zero L).weierstrassCurve_Δ_ne_zero⟩

theorem jLattice_eq_j (L : PeriodPair) : L.jLattice = L.weierstrassCurve.j := by
  rw [PeriodPair.jLattice_eq_c₄_pow_three_div_Δ, j_eq_div]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem complexCase (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (hN : NormFormulaAlong ℂ ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) E.j)).eval E'.j = 0 := by

  obtain ⟨L, C, hE⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E : WeierstrassCurve ℂ)
  obtain ⟨L', C', hE'⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E' : WeierstrassCurve ℂ)
  subst hE hE'

  haveI : IsDedekindDomain L.weierstrassCurve.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain L.weierstrassCurve
  haveI : IsDedekindDomain L'.weierstrassCurve.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain L'.weierstrassCurve
  haveI : HasPrincipalDivisors ℂ L.weierstrassCurve.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField L.weierstrassCurve.toAffine
  haveI : HasPrincipalDivisors ℂ L'.weierstrassCurve.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField L'.weierstrassCurve.toAffine
  obtain ⟨gL, hcL, haL⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
      (W := L.weierstrassCurve.toAffine)
  obtain ⟨gL', hcL', haL'⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
      (W := L'.weierstrassCurve.toAffine)
  letI := gL
  letI := gL'
  haveI := hcL
  haveI := haL
  haveI := hcL'
  haveI := haL'

  obtain ⟨eE⟩ := WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange L.weierstrassCurve C
  obtain ⟨eE'⟩ := WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange L'.weierstrassCurve C'

  have hι'' := conjSeam_isIntegral eE eE' ι hι
  have hfin'' := conjSeam_finiteAlong eE eE' ι hfin
  have hN'' : NormFormulaAlong ℂ (conjSeam eE eE' ι) hfin'' := normFormulaAlong_of_charZero _ hfin''

  obtain ⟨hcyc'', hcard''⟩ :=
    WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
      (C • L.weierstrassCurve).toAffine (C' • L'.weierstrassCurve).toAffine
      L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine
      ι hι hfin hN eE eE' (conjSeam eE eE' ι) (fun x => by
        rw [conjSeam_apply, AlgEquiv.apply_symm_apply]) hι'' hfin'' hN'' hcyc
  rw [hcard] at hcard''

  obtain ⟨β, hsub, hidx, hcycq⟩ :=
    PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
      L L' (conjSeam eE eE' ι) hι'' hfin'' hN'' N hcyc'' hcard''

  have hroot := ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic
    N data L (L'.scale β) hsub hidx hcycq
  rw [PeriodPair.jLattice_scale, jLattice_eq_j, jLattice_eq_j] at hroot

  have hj : WeierstrassCurve.j (C • L.weierstrassCurve) = L.weierstrassCurve.j :=
    WeierstrassCurve.variableChange_j _ _
  have hj' : WeierstrassCurve.j (C' • L'.weierstrassCurve) = L'.weierstrassCurve.j :=
    WeierstrassCurve.variableChange_j _ _
  have hjE : (show WeierstrassCurve.Affine ℂ from C • L.weierstrassCurve).j = L.weierstrassCurve.j := hj
  have hjE' : (show WeierstrassCurve.Affine ℂ from C' • L'.weierstrassCurve).j = L'.weierstrassCurve.j := hj'
  rw [hjE, hjE']
  exact hroot

end F4Proof
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.PeriodPair P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.F4Proof"

namespace F4Proof
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem solution0
    {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0 := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  obtain ⟨K₀, hK₀, E₀, E₀', hE₀, hE₀', hE, hE', hEb, hEb', ι₀, hι₀, hfin₀, H⟩ :=
    WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
      E E' ι hι hfin hN N hcyc hcard
  haveI := hE₀
  haveI := hE₀'
  haveI := hEb
  haveI := hEb'
  haveI : Countable K₀ := hK₀
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero
  haveI : CharZero (AlgebraicClosure K₀) :=
    charZero_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective
  haveI : DecidableEq (AlgebraicClosure K₀) := Classical.decEq _

  haveI : IsDedekindDomain (E₀.baseChange (AlgebraicClosure K₀)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : IsDedekindDomain (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : HasPrincipalDivisors (AlgebraicClosure K₀) (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  haveI : HasPrincipalDivisors (AlgebraicClosure K₀) (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g₁, c₁, a₁⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀.baseChange (AlgebraicClosure K₀)).toAffine)
  obtain ⟨g₂, c₂, a₂⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀'.baseChange (AlgebraicClosure K₀)).toAffine)
  letI := g₁
  letI := g₂
  haveI := c₁
  haveI := a₁
  haveI := c₂
  haveI := a₂
  have hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀ := normFormulaAlong_of_charZero ι₀ hfin₀
  obtain ⟨hcyc₀, hcard₀⟩ := H hN₀

  obtain ⟨φ₀⟩ := Field.nonempty_ringHom_complex_of_countable K₀
  letI : Algebra K₀ ℂ := φ₀.toAlgebra
  haveI : Module.IsTorsionFree K₀ ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ₀.injective
  haveI : Module.IsTorsionFree K₀ (AlgebraicClosure K₀) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K₀ (AlgebraicClosure K₀)).injective
  let σ : AlgebraicClosure K₀ →ₐ[K₀] ℂ := IsAlgClosed.lift
  haveI : (E₀.baseChange ℂ).IsElliptic := isElliptic_map E₀ _
  haveI : (E₀'.baseChange ℂ).IsElliptic := isElliptic_map E₀' _

  haveI : IsDedekindDomain (E₀.baseChange ℂ).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : IsDedekindDomain (E₀'.baseChange ℂ).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : HasPrincipalDivisors ℂ (E₀.baseChange ℂ).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  haveI : HasPrincipalDivisors ℂ (E₀'.baseChange ℂ).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g₃, c₃, a₃⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀.baseChange ℂ).toAffine)
  obtain ⟨g₄, c₄, a₄⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀'.baseChange ℂ).toAffine)
  letI := g₃
  letI := g₄
  haveI := c₃
  haveI := a₃
  haveI := c₄
  haveI := a₄

  obtain ⟨ι₁, hι₁, hfin₁, H₁⟩ :=
    WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
      K₀ E₀ E₀' (AlgebraicClosure K₀) ℂ σ ι₀ hι₀ hfin₀ hN₀ N hcyc₀ hcard₀
  have hN₁ : NormFormulaAlong ℂ ι₁ hfin₁ := normFormulaAlong_of_charZero ι₁ hfin₁
  obtain ⟨hcyc₁, hcard₁⟩ := H₁ hN₁

  have hC := complexCase (E₀.baseChange ℂ).toAffine (E₀'.baseChange ℂ).toAffine
    ι₁ hι₁ hfin₁ hN₁ N hcyc₁ hcard₁ data

  have hjC : WeierstrassCurve.j (E₀.baseChange ℂ).toAffine = φ₀ E₀.j := E₀.map_j φ₀
  have hjC' : WeierstrassCurve.j (E₀'.baseChange ℂ).toAffine = φ₀ E₀'.j := E₀'.map_j φ₀
  rw [hjC, hjC', ← map_eval_map_Φ] at hC
  have hK₀ : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K₀) E₀.j)).eval E₀'.j = 0 :=
    φ₀.injective (hC.trans (map_zero φ₀).symm)

  subst hE hE'
  have hjK : WeierstrassCurve.j (show WeierstrassCurve.Affine K from E₀.map (algebraMap K₀ K)) =
      algebraMap K₀ K E₀.j := E₀.map_j _
  have hjK' : WeierstrassCurve.j (show WeierstrassCurve.Affine K from E₀'.map (algebraMap K₀ K)) =
      algebraMap K₀ K E₀'.j := E₀'.map_j _
  rw [hjK, hjK', ← map_eval_map_Φ, hK₀, map_zero]

end F4Proof
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.PeriodPair P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.F4Proof"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.PeriodPair P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.F4Proof"

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem solution
    (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0 :=
  F4Proof.solution0 E E' ι hι hfin hN N hcyc hcard data

end S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
end P2MW
export P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward (solution)

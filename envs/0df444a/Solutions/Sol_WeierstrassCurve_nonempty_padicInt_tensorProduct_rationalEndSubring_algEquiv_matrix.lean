-- Prove2me | solution 1 for WeierstrassCurve.nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e1c979e2-8e35-5c19-afaa-9d4ca5894e61

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq
import Theorems.Thm_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
import Theorems.Thm_WeierstrassCurve_exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv
import Theorems.Thm_WeierstrassCurve_free_and_finrank_rationalEndSubring_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero FrobeniusEndo.linePencil_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"
open scoped TensorProduct

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map map_id IsIntegral toAffine Affine.Point Affine.Point.map Affine.Point.map_some minimal j evalEvalBC rationalHomSet rationalEndSubring card card_torsion_of_isAlgClosed tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv free_and_finrank_rationalEndSubring_eq_four"
namespace TateEndIso
p2m_open "WeierstrassCurve"

section MapT

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

noncomputable def mapT (f : M →+ M) : TateModule p M →ₗ[ℤ_[p]] TateModule p M where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, _root_.map_zero],
      by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change f ((x : ℕ → M) n + (y : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    exact map_add f _ _)
  map_smul' a x := Subtype.ext (funext fun n => by
    change f (((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → M) n)
    exact map_zsmul f _ _)

@[scoped simp] theorem mapT_apply (f : M →+ M) (x : TateModule p M) (n : ℕ) :
    ((mapT (p := p) f x : TateModule p M) : ℕ → M) n = f ((x : ℕ → M) n) := rfl

noncomputable def mapTRingHom : AddMonoid.End M →+* Module.End ℤ_[p] (TateModule p M) where
  toFun f := mapT (p := p) f
  map_one' := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_zero' := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

@[scoped simp] theorem mapTRingHom_apply (f : AddMonoid.End M) (x : TateModule p M) (n : ℕ) :
    ((mapTRingHom (p := p) f x : TateModule p M) : ℕ → M) n = f ((x : ℕ → M) n) := rfl

theorem intCast_smul_apply (c : ℤ) (x : TateModule p M) (n : ℕ) :
    (((c : ℤ_[p]) • x : TateModule p M) : ℕ → M) n = c • (x : ℕ → M) n := by
  rw [Int.cast_smul_eq_zsmul, AddSubgroupClass.coe_zsmul, Pi.smul_apply]

end MapT

section Finite

variable {K : Type*} [Field K] [Fintype K] {k : Type} [Field k] [DecidableEq k] [Algebra K k]
  [IsAlgClosed k]

omit [Fintype K] in

theorem hcard (W : WeierstrassCurve K) [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (n : ℕ) : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W (n := ℓ ^ n)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ)

theorem finite_case [Algebra.IsAlgebraic K k] (W : WeierstrassCurve K) [W.IsElliptic]
    (σ : k ≃ₐ[K] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card K) (a : ℤ)
    (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) (σ : k →ₐ[K] k) P = a • P)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    [Module.Free ℤ (rationalEndSubring k W)] [Module.Finite ℤ (rationalEndSubring k W)]
    (hrank : Module.finrank ℤ (rationalEndSubring k W) = 4) :
    Nonempty (ℤ_[ℓ] ⊗[ℤ] ↥(rationalEndSubring k W) ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
  classical
  have hℓk : (ℓ : k) ≠ 0 := by
    intro h
    apply hℓ
    apply (algebraMap K k).injective
    rw [map_natCast, h, _root_.map_zero]

  set M := (W⁄k).Point with hM
  set T := TateModule ℓ M with hT
  let b : Module.Basis (Fin 2) ℤ_[ℓ] T := TateModule.basisOfCard (hcard W ℓ hℓk)
  haveI : Module.Free ℤ_[ℓ] T := Module.Free.of_basis b
  haveI : Module.Finite ℤ_[ℓ] T := Module.Finite.of_basis b

  set R := rationalEndSubring k W with hR
  let ρ : R →+* Module.End ℤ_[ℓ] T := (mapTRingHom (p := ℓ)).comp R.subtype
  have hρ : ∀ (α : R) (x : T) (n : ℕ),
      ((ρ α x : T) : ℕ → M) n = (α : AddMonoid.End M) ((x : ℕ → M) n) := fun _ _ _ => rfl
  let θ : ℤ_[ℓ] ⊗[ℤ] R →ₐ[ℤ_[ℓ]] Module.End ℤ_[ℓ] T :=
    Algebra.TensorProduct.lift (Algebra.ofId ℤ_[ℓ] _) ρ.toIntAlgHom
      (fun c α => Algebra.commutes c _)
  have hθ : ∀ (c : ℤ_[ℓ]) (α : R), θ (c ⊗ₜ α) = c • ρ α := fun c α => by
    change (Algebra.ofId ℤ_[ℓ] _ c) * ρ α = c • ρ α
    rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

  have hrep : TateModule.rep ℓ M (k ≃ₐ[K] k) σ = (a : ℤ_[ℓ]) • (1 : Module.End ℤ_[ℓ] T) := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [TateModule.rep_apply, LinearMap.smul_apply, intCast_smul_apply]
    exact ha _

  have hsurj : Function.Surjective θ := by
    intro Φ
    have hΦ : Φ ∘ₗ TateModule.rep ℓ M (k ≃ₐ[K] k) σ = TateModule.rep ℓ M (k ≃ₐ[K] k) σ ∘ₗ Φ := by
      rw [hrep, LinearMap.comp_smul, LinearMap.smul_comp, Module.End.one_eq_id, LinearMap.comp_id,
        LinearMap.id_comp]
    obtain ⟨m, α, c, Ψ, hα, hΨ, hsum⟩ :
        ∃ (m : ℕ) (α : Fin m → (M →+ M)) (c : Fin m → ℤ_[ℓ]) (Ψ : Fin m → (T →ₗ[ℤ_[ℓ]] T)),
          (∀ j, α j ∈ WeierstrassCurve.rationalHomSet k W W) ∧
          (∀ j (x : T) (n : ℕ), ((Ψ j x : T) : ℕ → M) n = α j ((x : ℕ → M) n)) ∧
          Φ = ∑ j, c j • Ψ j := by
      by_cases ht : ((Fintype.card K : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 =
          4 * (Fintype.card K : ℤ)
      · exact WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq
          W σ hσ ℓ hℓ ht Φ hΦ
      · exact WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
          W σ hσ ℓ hℓ ht Φ hΦ
    refine ⟨∑ j, c j ⊗ₜ ⟨α j, Subring.subset_closure (hα j)⟩, ?_⟩
    rw [map_sum, hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθ]
    congr 1
    exact LinearMap.ext fun x => Subtype.ext (funext fun n => (hΨ j x n).symm)

  haveI : Module.Finite ℤ_[ℓ] (Module.End ℤ_[ℓ] T) := Module.Finite.linearMap _ _ _ _
  have hinj : Function.Injective θ := by

    let bR := Module.Free.chooseBasis ℤ R
    let bTR : Module.Basis (Module.Free.ChooseBasisIndex ℤ R) ℤ_[ℓ] (ℤ_[ℓ] ⊗[ℤ] R) :=
      Algebra.TensorProduct.basis ℤ_[ℓ] bR
    let bE : Module.Basis (Fin 2 × Fin 2) ℤ_[ℓ] (Module.End ℤ_[ℓ] T) :=
      (Matrix.stdBasis ℤ_[ℓ] (Fin 2) (Fin 2)).map (LinearMap.toMatrix b b).symm
    have hcardι : Fintype.card (Module.Free.ChooseBasisIndex ℤ R) = Fintype.card (Fin 2 × Fin 2) := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]; simp
    let i : ℤ_[ℓ] ⊗[ℤ] R ≃ₗ[ℤ_[ℓ]] Module.End ℤ_[ℓ] T := bTR.equiv bE (Fintype.equivOfCardEq hcardι)
    exact OrzechProperty.injective_of_surjective_of_injective i.toLinearMap θ.toLinearMap
      i.injective hsurj
  exact ⟨(AlgEquiv.ofBijective θ ⟨hinj, hsurj⟩).trans (LinearMap.toMatrixAlgEquiv b)⟩

end Finite

section TypeZero

theorem type_zero_case {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    Nonempty (ℤ_[ℓ] ⊗[ℤ] ↥(rationalEndSubring k X) ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
  obtain ⟨K, instF, W, instE, σ₀, a, hσ₀, ha, ⟨eR⟩⟩ :=
    WeierstrassCurve.exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv p X hss
  obtain ⟨hfree, hfin, hrank⟩ :=
    WeierstrassCurve.free_and_finrank_rationalEndSubring_eq_four p X hss

  let eL : ↥(rationalEndSubring k X) ≃ₗ[ℤ] ↥(rationalEndSubring k W) :=
    eR.toAddEquiv.toIntLinearEquiv
  haveI : Module.Free ℤ ↥(rationalEndSubring k W) := Module.Free.of_equiv eL
  haveI : Module.Finite ℤ ↥(rationalEndSubring k W) := Module.Finite.equiv eL
  have hrank' : Module.finrank ℤ ↥(rationalEndSubring k W) = 4 := by
    rw [← eL.finrank_eq, hrank]

  haveI : Algebra.IsAlgebraic K k := by

    refine ⟨fun x => ?_⟩
    have hx : _root_.IsIntegral (ZMod p) x := Algebra.IsIntegral.isIntegral x
    obtain ⟨F, hFmap, -, hFmonic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic
        (Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) _
          |> fun ⟨G, hG⟩ => (Polynomial.mem_lifts _).mpr ⟨G, hG⟩) (minpoly.monic hx)
    have hxZ : _root_.IsIntegral ℤ x := by
      refine ⟨F, hFmonic, ?_⟩
      have h1 : Polynomial.aeval x (minpoly (ZMod p) x) = 0 := minpoly.aeval _ _
      rw [← hFmap, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap] at h1
      exact h1
    exact (hxZ.tower_top (A := K)).isAlgebraic

  let σ : k ≃ₐ[K] k := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  have hσcoe : (σ : k →ₐ[K] k) = σ₀ := AlgHom.ext fun _ => rfl
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h
    have hk : (ℓ : k) = 0 := by
      have := congrArg (algebraMap K k) h
      rwa [map_natCast, _root_.map_zero] at this
    rw [CharP.cast_eq_zero_iff k p] at hk
    exact hℓ (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp hk).symm)
  obtain ⟨e⟩ := finite_case W σ hσ₀ a (fun P => by rw [hσcoe]; exact ha P) ℓ hℓK hrank'
  refine ⟨(Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofRingEquiv (f := eR) ?_)).trans e⟩
  intro n
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]

end TypeZero

section Transport

open Polynomial
open scoped Polynomial.Bivariate

universe u v

variable {k : Type u} {k' : Type v} [Field k] [Field k']

def conjRingEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A ≃+ B) :
    AddMonoid.End A ≃+* AddMonoid.End B where
  toFun α := φ.toAddMonoidHom.comp (α.comp φ.symm.toAddMonoidHom)
  invFun β := φ.symm.toAddMonoidHom.comp (β.comp φ.toAddMonoidHom)
  left_inv α := AddMonoidHom.ext fun x =>
    show φ.symm (φ (α (φ.symm (φ x)))) = α x by rw [φ.symm_apply_apply, φ.symm_apply_apply]
  right_inv β := AddMonoidHom.ext fun x =>
    show φ (φ.symm (β (φ (φ.symm x)))) = β x by rw [φ.apply_symm_apply, φ.apply_symm_apply]
  map_mul' α β := AddMonoidHom.ext fun x =>
    show φ (α (β (φ.symm x))) = φ (α (φ.symm (φ (β (φ.symm x))))) by rw [φ.symm_apply_apply]
  map_add' α β := AddMonoidHom.ext fun x =>
    show φ (α (φ.symm x) + β (φ.symm x)) = φ (α (φ.symm x)) + φ (β (φ.symm x)) from map_add φ _ _

theorem conjRingEquiv_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A ≃+ B)
    (α : AddMonoid.End A) :
    conjRingEquiv φ α = φ.toAddMonoidHom.comp (α.comp φ.symm.toAddMonoidHom) := rfl

theorem evalEvalBC_self (q : k[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k q x y = q.evalEval x y := by
  unfold WeierstrassCurve.evalEvalBC
  rw [Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

theorem map_evalEvalBC (e : k →+* k') (q : k[X][Y]) (x y : k) :
    e (WeierstrassCurve.evalEvalBC k q x y) =
      WeierstrassCurve.evalEvalBC k' (q.map (mapRingHom e)) (e x) (e y) := by
  rw [evalEvalBC_self, evalEvalBC_self, Polynomial.map_mapRingHom_evalEval]

variable [DecidableEq k] [DecidableEq k']

omit [DecidableEq k] in
theorem some_congr {X : WeierstrassCurve k} {x₁ y₁ x₂ y₂ : k} {h₁ : X.toAffine.Nonsingular x₁ y₁}
    {h₂ : X.toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (.some x₁ y₁ h₁ : X.toAffine.Point) = .some x₂ y₂ h₂ := by
  subst hx hy; rfl

omit [DecidableEq k] in
theorem exists_some_of_eq {X : WeierstrassCurve k} {Q : X.toAffine.Point} {x₁ y₁ x₂ y₂ : k}
    {h₁ : X.toAffine.Nonsingular x₁ y₁} (hQ : Q = .some x₁ y₁ h₁) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

theorem conj_mem_rationalHomSet (X : WeierstrassCurve k) (X' : WeierstrassCurve k') (e : k →+* k')
    (φ : X.toAffine.Point →+ X'.toAffine.Point) (ψ : X'.toAffine.Point →+ X.toAffine.Point)
    (hφ : ∀ (x y : k) (h : X.toAffine.Nonsingular x y), ∃ h', φ (.some x y h) = .some (e x) (e y) h')
    (hψ : ∀ (x' y' : k') (h' : X'.toAffine.Nonsingular x' y'),
      ∃ (x y : k) (h : X.toAffine.Nonsingular x y),
        ψ (.some x' y' h') = .some x y h ∧ e x = x' ∧ e y = y')
    {α : X.toAffine.Point →+ X.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k X X) :
    φ.comp (α.comp ψ) ∈ WeierstrassCurve.rationalHomSet k' X' X' := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · left
    show φ.comp ((0 : X.toAffine.Point →+ X.toAffine.Point).comp ψ) = 0
    rw [AddMonoidHom.zero_comp, AddMonoidHom.comp_zero]
  right
  refine ⟨nX.map (mapRingHom e), dX.map (mapRingHom e), nY.map (mapRingHom e),
    dY.map (mapRingHom e), e '' B, hB.image e, fun x' y' h' hx' => ?_⟩
  obtain ⟨x, y, h, hψP, hx, hy⟩ := hψ x' y' h'
  subst hx hy
  have hxB : x ∉ B := fun hb => hx' ⟨x, hb, rfl⟩
  obtain ⟨hd1, hd2, h'', hαP⟩ := hrep x y h hxB
  replace hαP : α (.some x y h) = .some _ _ h'' := hαP
  obtain ⟨h₄, hφP⟩ := hφ _ _ h''
  refine ⟨by rw [← map_evalEvalBC]; exact (map_ne_zero e).mpr hd1,
    by rw [← map_evalEvalBC]; exact (map_ne_zero e).mpr hd2, ?_⟩
  refine exists_some_of_eq (h₁ := h₄) ?_ ?_ ?_
  · change φ (α (ψ (.some (e x) (e y) h'))) = _
    rw [hψP, hαP, hφP]
    rfl
  · rw [map_div₀, map_evalEvalBC, map_evalEvalBC]
  · rw [map_div₀, map_evalEvalBC, map_evalEvalBC]

theorem transport (e : k ≃+* k') (X : WeierstrassCurve k) :
    Nonempty (X.toAffine.Point ≃+ (X.map e.toRingHom).toAffine.Point) ∧
      Nonempty (↥(WeierstrassCurve.rationalEndSubring k X) ≃+*
        ↥(WeierstrassCurve.rationalEndSubring k' (X.map e.toRingHom))) := by
  letI : Algebra k k' := e.toRingHom.toAlgebra
  let f : k →ₐ[k] k' := { e.toRingHom with commutes' := fun _ => rfl }
  let g : k' →ₐ[k] k := { e.symm.toRingHom with commutes' := fun r => e.symm_apply_apply r }
  let φ₀ : (X⁄k).Point →+ (X⁄k').Point := WeierstrassCurve.Affine.Point.map (W' := X) f
  let ψ₀ : (X⁄k').Point →+ (X⁄k).Point := WeierstrassCurve.Affine.Point.map (W' := X) g
  have hψφ : ∀ P, ψ₀ (φ₀ P) = P := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · change WeierstrassCurve.Affine.Point.map g (WeierstrassCurve.Affine.Point.map f (.some x y h)) = _
      rw [WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.map_some]
      exact some_congr (e.symm_apply_apply x) (e.symm_apply_apply y)
  have hφψ : ∀ P, φ₀ (ψ₀ P) = P := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · change WeierstrassCurve.Affine.Point.map f (WeierstrassCurve.Affine.Point.map g (.some x y h)) = _
      rw [WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.map_some]
      exact some_congr (e.apply_symm_apply x) (e.apply_symm_apply y)
  let φ : (X⁄k).Point ≃+ (X⁄k').Point :=
    { toFun := φ₀, invFun := ψ₀, left_inv := hψφ, right_inv := hφψ, map_add' := φ₀.map_add }
  have hφsome : ∀ (x y : k) (h : (X⁄k).Nonsingular x y),
      ∃ h', φ₀ (.some x y h) = .some (e x) (e y) h' := fun x y h =>
    ⟨_, WeierstrassCurve.Affine.Point.map_some f h⟩
  have hψsome : ∀ (x' y' : k') (h' : (X⁄k').Nonsingular x' y'),
      ∃ h, ψ₀ (.some x' y' h') = .some (e.symm x') (e.symm y') h := fun x' y' h' =>
    ⟨_, WeierstrassCurve.Affine.Point.map_some g h'⟩

  let C : AddMonoid.End (X⁄k).Point ≃+* AddMonoid.End (X⁄k').Point := conjRingEquiv φ
  have hC : ∀ α, C α = φ₀.comp (α.comp ψ₀) := fun α => rfl
  have hCsymm : ∀ β, C.symm β = ψ₀.comp (β.comp φ₀) := fun β => rfl
  have himage : (C : AddMonoid.End (X⁄k).Point → AddMonoid.End (X⁄k').Point) ''
      WeierstrassCurve.rationalHomSet k X X =
        WeierstrassCurve.rationalHomSet k' (X.map e.toRingHom) (X.map e.toRingHom) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨α, hα, rfl⟩
      rw [hC]
      exact conj_mem_rationalHomSet X (X.map e.toRingHom) e.toRingHom φ₀ ψ₀ hφsome
        (fun x' y' h' => ⟨e.symm x', e.symm y', _, (hψsome x' y' h').choose_spec,
          e.apply_symm_apply x', e.apply_symm_apply y'⟩) hα
    · intro β hβ
      refine ⟨C.symm β, ?_, C.apply_symm_apply β⟩
      rw [hCsymm]
      exact conj_mem_rationalHomSet (X.map e.toRingHom) X e.symm.toRingHom ψ₀ φ₀ hψsome
        (fun x y h => ⟨e x, e y, _, (hφsome x y h).choose_spec,
          e.symm_apply_apply x, e.symm_apply_apply y⟩) hβ
  have hmap : (WeierstrassCurve.rationalEndSubring k X).map C.toRingHom =
      WeierstrassCurve.rationalEndSubring k' (X.map e.toRingHom) := by
    unfold WeierstrassCurve.rationalEndSubring
    rw [RingHom.map_closure]
    exact congrArg Subring.closure himage
  exact ⟨⟨φ⟩, ⟨(C.subringMap (s := WeierstrassCurve.rationalEndSubring k X)).trans
    (RingEquiv.subringCongr hmap)⟩⟩

end Transport

end WeierstrassCurve.TateEndIso
p2m_reactivate "P2MW.S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix.WeierstrassCurve P2MW.S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix.WeierstrassCurve.TateEndIso"
p2m_reactivate "P2MW.S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix.WeierstrassCurve"

open WeierstrassCurve.TateEndIso in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    Nonempty (ℤ_[ℓ] ⊗[ℤ] ↥(WeierstrassCurve.rationalEndSubring k X) ≃ₐ[ℤ_[ℓ]]
      Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
  let k₀ : Type := AlgebraicClosure (ZMod p)
  letI : DecidableEq k₀ := Classical.decEq _
  haveI : IsAlgClosure (ZMod p) k := ⟨inferInstance, inferInstance⟩
  let e : k ≃ₐ[ZMod p] k₀ := IsAlgClosure.equiv (ZMod p) k k₀
  obtain ⟨⟨φ⟩, ⟨eR⟩⟩ := transport e.toRingEquiv X
  have hss₀ : ∀ P : (X.map e.toRingEquiv.toRingHom).toAffine.Point, p • P = 0 → P = 0 := by
    intro P hP
    apply φ.symm.injective
    rw [_root_.map_zero]
    apply hss
    rw [← map_nsmul, hP, _root_.map_zero]
  obtain ⟨e₀⟩ := type_zero_case p (X.map e.toRingEquiv.toRingHom) hss₀ ℓ hℓ
  refine ⟨(Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofRingEquiv (f := eR) ?_)).trans e₀⟩
  intro n
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]

end S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix
end P2MW
export P2MW.S_WeierstrassCurve_nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix (solution)

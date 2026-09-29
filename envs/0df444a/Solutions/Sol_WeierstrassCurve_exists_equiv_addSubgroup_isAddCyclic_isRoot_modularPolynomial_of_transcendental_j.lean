-- Prove2me | solution 1 for WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e671b100-78f2-576f-be4c-c5c6b790c642

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

open ModularCurve WeierstrassCurve Polynomial IntermediateField

namespace P2MKcKIV

universe u v

theorem separable_fibre (K : Type u) [Field K] {F : Type v} [Field F] [Algebra K F]
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (hNK : (N : K) ≠ 0)
    (x : F) (hx : Transcendental K x) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x)).Separable := by

  set φ : Polynomial K →+* F := (Polynomial.aeval (R := K) x).toRingHom with hφ
  have hφinj : Function.Injective φ := transcendental_iff_injective.1 hx
  have hφ0 : nonZeroDivisors (Polynomial K) ≤ (nonZeroDivisors F).comap φ := fun p hp =>
    mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hφinj (h.trans (map_zero φ).symm)))
  set ψ : RatFunc K →+* F := RatFunc.liftRingHom φ hφ0
  have hsep := (data.separable_map_ratFunc_of_natCast_ne_zero K N hNK).map (f := ψ)
  rw [Polynomial.map_map, Polynomial.map_map] at hsep
  convert hsep using 2
  refine Polynomial.ringHom_ext ?_ ?_
  · intro n
    simp [ψ, φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    change x = ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
    rw [RatFunc.liftRingHom_algebraMap]
    simp [φ]

theorem mem_range_of_fixed {Ω : Type u} [Field Ω] {M : Type v} [Field M] [Algebra Ω M]
    [IsAlgClosure Ω M] (α : M) (p : Polynomial Ω) (hsep : p.Separable)
    (hroot : (p.map (algebraMap Ω M)).IsRoot α)
    (hfix : ∀ τ : M ≃ₐ[Ω] M, τ α = α) : α ∈ Set.range (algebraMap Ω M) := by
  haveI : IsAlgClosed M := IsAlgClosure.isAlgClosed Ω
  haveI : Algebra.IsAlgebraic Ω M := IsAlgClosure.isAlgebraic
  haveI : Normal Ω M := ⟨fun x => IsAlgClosed.splits _⟩
  have hint : IsIntegral Ω α := Algebra.IsIntegral.isIntegral α

  have hmin_dvd : minpoly Ω α ∣ p := minpoly.dvd Ω α (by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hroot)
  have hmin_sep : (minpoly Ω α).Separable := hsep.of_dvd hmin_dvd

  have hroots : ∀ β : M, (minpoly Ω α).map (algebraMap Ω M) |>.IsRoot β → β = α := by
    intro β hβ

    have hβ' : β ∈ ((minpoly Ω α).map (algebraMap Ω M)).roots :=
      (Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).2 hβ
    let f₀ : Ω⟮α⟯ →ₐ[Ω] M :=
      (IntermediateField.algHomAdjoinIntegralEquiv Ω hint).symm ⟨β, hβ'⟩
    have hf₀ : f₀ (IntermediateField.AdjoinSimple.gen Ω α) = β :=
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen Ω hint _

    let f₁ : M →ₐ[Ω] M := f₀.liftNormal M
    let τ : M ≃ₐ[Ω] M := AlgEquiv.ofBijective f₁ (Algebra.IsAlgebraic.algHom_bijective f₁)
    have hτ : τ α = β := by
      change f₁ α = β
      have := AlgHom.liftNormal_commutes f₀ M (IntermediateField.AdjoinSimple.gen Ω α)
      rw [IntermediateField.AdjoinSimple.algebraMap_gen] at this
      change f₁ α = algebraMap M M (f₀ _) at this
      rw [this, hf₀]; rfl
    rw [← hτ, hfix τ]

  have hsplit : ((minpoly Ω α).map (algebraMap Ω M)).Splits := IsAlgClosed.splits _
  have hcard : ((minpoly Ω α).map (algebraMap Ω M)).roots.card = (minpoly Ω α).natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap Ω M)]
    exact (Polynomial.splits_iff_card_roots.1 hsplit)
  have hnodup : ((minpoly Ω α).map (algebraMap Ω M)).roots.Nodup :=
    Polynomial.nodup_roots hmin_sep.map
  have hall : ∀ b ∈ ((minpoly Ω α).map (algebraMap Ω M)).roots, b = α := fun β hβ =>
    hroots β ((Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).1 hβ)
  have hrep := Multiset.eq_replicate_card.2 hall
  have hle : ((minpoly Ω α).map (algebraMap Ω M)).roots.card ≤ 1 := by
    classical
    have hc := (Multiset.nodup_iff_count_le_one.1 hnodup) α
    rw [hrep, Multiset.count_replicate_self] at hc
    exact hc
  have hdeg : (minpoly Ω α).natDegree = 1 := by
    have h1 : 0 < (minpoly Ω α).natDegree := minpoly.natDegree_pos hint
    omega

  have := minpoly.mem_range_of_degree_eq_one Ω α (by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hdeg]; rfl)
  exact this

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k M : Type*} [Field k] [Field M] [Algebra k M]
    [IsAlgClosed M] [DecidableEq M] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : M) ≠ 0) :
    Nat.card {Q : (E.baseChange M).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := M) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem nsmul_eq_zero_of_mem {A : Type*} [AddCommGroup A] {H : AddSubgroup A} {N : ℕ}
    (hH : Nat.card H = N) {P : A} (hP : P ∈ H) : N • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH] at this
  exact congrArg Subtype.val this

end P2MKcKIV

open P2MKcKIV in
universe u v in
theorem solution (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra k Ω]
    (hN : (N : k) ≠ 0) (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Θ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω)
          (algebraMap k Ω E.j))).IsRoot y},
      ∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Θ H').1 : Ω) = σ (Θ H).1 := by
  classical

  let M := AlgebraicClosure Ω
  let ι : Ω →ₐ[k] M := IsScalarTower.toAlgHom k Ω M
  have hιalg : ∀ x : Ω, ι x = algebraMap Ω M x := fun x => rfl
  have hιinj : Function.Injective ι := (algebraMap Ω M).injective
  let ιp : (E.baseChange Ω).toAffine.Point →+ (E.baseChange M).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map ι
  have hιp : Function.Injective ιp := WeierstrassCurve.Affine.Point.map_injective ι

  letI : Algebra K Ω := ((algebraMap k Ω).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K Ω M := AlgebraicClosure.instIsScalarTower Ω
  haveI : IsScalarTower K k M := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K Ω M, IsScalarTower.algebraMap_apply k Ω M]
    rfl
  have hNK : (N : K) ≠ 0 := fun h => hN (by simpa using congrArg (algebraMap K k) h)
  have hNΩ : (N : Ω) ≠ 0 := fun h => hN ((algebraMap k Ω).injective (by simpa using h))
  have hNM : (N : M) ≠ 0 := fun h => hNΩ ((algebraMap Ω M).injective (by simpa using h))

  set x : Ω := algebraMap k Ω E.j with hx
  set pΩ : Polynomial Ω := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x) with hpΩ
  have hxT : Transcendental K x := (transcendental_algebraMap_iff (algebraMap k Ω).injective).2 hE
  have hsep : pΩ.Separable := separable_fibre K N data hNK x hxT
  haveI instEM : (E.baseChange M).IsElliptic :=
    show (E.map (algebraMap k M)).IsElliptic from inferInstance
  have hjM : (E.baseChange M).j = algebraMap Ω M x := by
    change (E.map (algebraMap k M)).j = _
    rw [WeierstrassCurve.map_j, hx, ← IsScalarTower.algebraMap_apply]
  have hEM : Transcendental K (E.baseChange M).j := by
    rw [hjM]
    exact (transcendental_algebraMap_iff (algebraMap Ω M).injective).2 hxT
  have hpM : pΩ.map (algebraMap Ω M) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom M) (E.baseChange M).j) := by
    rw [hpΩ, Polynomial.map_map, hjM]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp

  set F : AddSubgroup (E.baseChange M).toAffine.Point → M :=
    fun H => (E.baseChange M).cyclicQuotientJ H N with hF
  have hbij := WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
    K N data M hNM (E.baseChange M) hEM
  rw [← hpM] at hbij

  have htorM := natCard_torsion_of_isAlgClosed (M := M) E N hNM
  have hhit : ∀ Q : (E.baseChange M).toAffine.Point, N • Q = 0 → ∃ P, N • P = 0 ∧ ιp P = Q :=
    exists_eq_of_nsmul_eq_zero ιp hιp N hfull htorM

  have hmapS : ∀ H : AddSubgroup (E.baseChange Ω).toAffine.Point,
      IsAddCyclic H ∧ Nat.card H = N → IsAddCyclic (H.map ιp) ∧ Nat.card (H.map ιp) = N := by
    intro H ⟨hc, hcard⟩
    let e := H.equivMapOfInjective ιp hιp
    exact ⟨isAddCyclic_of_surjective e e.surjective, by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm⟩
  have hcomapS : ∀ H' : AddSubgroup (E.baseChange M).toAffine.Point,
      IsAddCyclic H' ∧ Nat.card H' = N →
        (H'.comap ιp).map ιp = H' ∧ IsAddCyclic (H'.comap ιp) ∧ Nat.card (H'.comap ιp) = N := by
    intro H' ⟨hc, hcard⟩
    have hle : H' ≤ ιp.range := fun Q hQ => by
      obtain ⟨P, -, hP⟩ := hhit Q (nsmul_eq_zero_of_mem hcard hQ)
      exact ⟨P, hP⟩
    have hmap : (H'.comap ιp).map ιp = H' := by
      rw [AddSubgroup.map_comap_eq, inf_eq_right.2 hle]
    let e := (H'.comap ιp).equivMapOfInjective ιp hιp
    have e' : (H'.comap ιp) ≃+ H' := e.trans (AddEquiv.addSubgroupCongr hmap)
    exact ⟨hmap, isAddCyclic_of_surjective e'.symm e'.symm.surjective,
      by rw [← hcard]; exact Nat.card_congr e'.toEquiv⟩

  have hfixed : ∀ (H : AddSubgroup (E.baseChange Ω).toAffine.Point) (τ : M ≃ₐ[Ω] M),
      τ (F (H.map ιp)) = F (H.map ιp) := by
    intro H τ
    let τk : M →ₐ[k] M := (τ : M →ₐ[Ω] M).restrictScalars k
    have hnat := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E τk (H.map ιp) N
    have hcomp : τk.comp ι = ι := by
      ext y
      change τ (ι y) = ι y
      rw [hιalg]; exact τ.commutes y
    have hHH : (H.map ιp).map (WeierstrassCurve.Affine.Point.map τk) = H.map ιp := by
      rw [AddSubgroup.map_map]
      congr 1
      ext P
      change WeierstrassCurve.Affine.Point.map τk (WeierstrassCurve.Affine.Point.map ι P) = _
      rw [WeierstrassCurve.Affine.Point.map_map, hcomp]
    rw [hHH] at hnat
    exact hnat.symm

  have hdesc : ∀ H : AddSubgroup (E.baseChange Ω).toAffine.Point, IsAddCyclic H ∧ Nat.card H = N →
      ∃ y : Ω, pΩ.IsRoot y ∧ algebraMap Ω M y = F (H.map ιp) := by
    intro H hH
    have hroot : (pΩ.map (algebraMap Ω M)).IsRoot (F (H.map ιp)) := hbij.mapsTo (hmapS H hH)
    obtain ⟨y, hy⟩ := mem_range_of_fixed (F (H.map ιp)) pΩ hsep hroot (hfixed H)
    refine ⟨y, ?_, hy⟩
    rw [← hy, Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom,
      map_eq_zero_iff _ (algebraMap Ω M).injective] at hroot
    exact hroot

  let Θ₀ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
      {y : Ω // pΩ.IsRoot y} := fun H => ⟨(hdesc H.1 H.2).choose, (hdesc H.1 H.2).choose_spec.1⟩
  have hΘ₀ : ∀ H, algebraMap Ω M (Θ₀ H).1 = F (H.1.map ιp) := fun H => (hdesc H.1 H.2).choose_spec.2
  have hinj : Function.Injective Θ₀ := by
    intro H₁ H₂ h
    have h' := congrArg (fun y : {y : Ω // pΩ.IsRoot y} => algebraMap Ω M y.1) h
    simp only [hΘ₀] at h'
    have := hbij.injOn (hmapS _ H₁.2) (hmapS _ H₂.2) h'
    exact Subtype.ext (AddSubgroup.map_injective hιp this)
  have hsurj : Function.Surjective Θ₀ := by
    rintro ⟨y, hy⟩
    have hyM : (pΩ.map (algebraMap Ω M)).IsRoot (algebraMap Ω M y) := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom, hy.eq_zero, map_zero]
    obtain ⟨H', hH', hFy⟩ := hbij.surjOn hyM
    obtain ⟨hmap, hc, hcard⟩ := hcomapS H' hH'
    refine ⟨⟨H'.comap ιp, hc, hcard⟩, Subtype.ext ((algebraMap Ω M).injective ?_)⟩
    rw [hΘ₀]
    change F ((H'.comap ιp).map ιp) = _
    rw [hmap]
    exact hFy
  refine ⟨Equiv.ofBijective Θ₀ ⟨hinj, hsurj⟩, ?_⟩

  intro σ H H' hH'
  change (Θ₀ H').1 = σ (Θ₀ H).1
  apply (algebraMap Ω M).injective

  let σM : M ≃+* M := IsAlgClosure.equivOfEquiv M M (σ : Ω ≃+* Ω)
  have hσM : ∀ y : Ω, σM (algebraMap Ω M y) = algebraMap Ω M (σ y) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap M M (σ : Ω ≃+* Ω) y
  let σk : M ≃ₐ[k] M := AlgEquiv.ofRingEquiv (f := σM) fun c => by
    rw [IsScalarTower.algebraMap_apply k Ω M, hσM, AlgEquiv.commutes]
  have hnat := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E
    (σk : M →ₐ[k] M) (H.1.map ιp) N
  have hcomp : (σk : M →ₐ[k] M).comp ι = ι.comp (σ : Ω →ₐ[k] Ω) := by
    ext y
    exact hσM y
  have hHH : (H.1.map ιp).map (WeierstrassCurve.Affine.Point.map (σk : M →ₐ[k] M)) =
      H'.1.map ιp := by
    rw [hH', AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext P
    change WeierstrassCurve.Affine.Point.map (σk : M →ₐ[k] M) (WeierstrassCurve.Affine.Point.map ι P)
      = WeierstrassCurve.Affine.Point.map ι (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P)
    rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map, hcomp]
  have e1 : F (H'.1.map ιp) = σk (F (H.1.map ιp)) := by rw [← hHH]; exact hnat
  rw [hΘ₀ H', e1, ← hΘ₀ H]
  exact hσM _

end S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
end P2MW
export P2MW.S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j (solution)

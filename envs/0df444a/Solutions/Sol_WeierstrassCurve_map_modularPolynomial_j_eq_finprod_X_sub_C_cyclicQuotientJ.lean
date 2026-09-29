-- Prove2me | solution 1 for WeierstrassCurve.map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/dec2f476-4752-582b-99a8-3edcce9ca1ab

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
import Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ.WeierstrassCurve IsLocalRing Polynomial ModularCurve"

universe u

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_c₄ a₃ map_map a₁ map coe_Δ' a₄ a₂ a₆ ofJ_j Affine.Point.map_injective ofJ reduction IsIntegral toAffine Affine.Point map_injective map_Δ map_a₆ Affine.Point.map map_a₁ map_a₄ Δ c₄ map_a₂ baseChange j Δ' map_a₃ cyclicQuotientJ reduceHom Affine.Y_mem_of_X_mem Affine.nonsingular_residue reducePoint_some_of_mem bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed eq_of_reduceHom_eq_of_nsmul_eq_zero"
p2m_open "WeierstrassCurve"
namespace LangSplit

section Poly

variable {R : Type*} [CommRing R]

abbrev fib (Φ : Polynomial (Polynomial ℤ)) (a : R) : Polynomial R :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)

theorem fib_map {S : Type*} [CommRing S] (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S) (a : R) :
    (fib Φ a).map f = fib Φ (f a) := by
  rw [fib, fib, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]

theorem eq_finprod_of_bijOn {p : Polynomial Ω} (hp : p.Monic) {ι : Type*} {S : Set ι} (c : ι → Ω)
    (hbij : Set.BijOn c S {y | p.IsRoot y}) (hcard : Nat.card S = p.natDegree) :
    p = ∏ᶠ i ∈ S, (X - C (c i)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set Rt : Finset Ω := p.roots.toFinset with hRt
  have hRt' : ({y | p.IsRoot y} : Set Ω) = ↑Rt := by
    ext y; rw [hRt, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0]; rfl
  have hcardR : Rt.card = p.roots.card := by
    have h1 : Nat.card ({y | p.IsRoot y} : Set Ω) = Nat.card S := (Nat.card_congr (hbij.equiv c)).symm
    rw [hRt', Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
    rw [h1, hcard]
    exact (IsAlgClosed.splits p).natDegree_eq_card_roots
  have hnodup : p.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.1 hcardR
  have hval : Rt.val = p.roots := by rw [hRt, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnodup]
  calc p = (p.roots.map fun x => X - C x).prod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
    _ = ∏ r ∈ Rt, (X - C r) := by rw [Finset.prod_eq_multiset_prod, hval]
    _ = ∏ᶠ r ∈ ({y | p.IsRoot y} : Set Ω), (X - C r) := by rw [hRt', finprod_mem_coe_finset]
    _ = ∏ᶠ i ∈ S, (X - C (c i)) := (finprod_mem_eq_of_bijOn c hbij fun _ _ => rfl).symm

end Poly

section Groups

abbrev CycSub (G : Type*) [AddCommGroup G] (n : ℕ) : Set (AddSubgroup G) :=
  {H | IsAddCyclic H ∧ Nat.card H = n}

theorem natCard_cycSub {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve k) [E.IsElliptic] {n : ℕ} [NeZero n] (hn : (n : Ω) ≠ 0) :
    Nat.card (CycSub (E.baseChange Ω).toAffine.Point n) = dedekindPsi n := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hn
  have := AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy n e
  rw [← this]
  exact Nat.card_congr (Equiv.refl _)

theorem dedekindPsi_pos {M : ℕ} (hM : M ≠ 0) : 0 < dedekindPsi M := by
  rw [dedekindPsi]
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
  · simp [hM]
  · rw [Nat.div_one]; exact Nat.pos_of_ne_zero hM

theorem nsmul_eq_zero_of_mem_cycSub {G : Type*} [AddCommGroup G] {n : ℕ} {H : AddSubgroup G}
    (hH : H ∈ CycSub G n) {P : G} (hP : P ∈ H) : n • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH.2] at this
  exact congrArg Subtype.val this

theorem map_mem_cycSub_of_injOn {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    {n : ℕ} {H : AddSubgroup G} (hH : H ∈ CycSub G n) (hf : Set.InjOn f H) :
    H.map f ∈ CycSub G' n := by
  haveI := hH.1
  refine ⟨isAddCyclic_of_surjective (f.addSubgroupMap H) (f.addSubgroupMap_surjective H), ?_⟩
  rw [← hH.2, ← SetLike.coe_sort_coe (H.map f), AddSubgroup.coe_map, Nat.card_image_of_injOn hf,
    SetLike.coe_sort_coe]

theorem bijOn_of_injOn_of_card_eq {α β : Type*} {s : Set α} {t : Set β} (f : α → β)
    (hmaps : Set.MapsTo f s t) (hinj : Set.InjOn f s) [Finite t] (hcard : Nat.card s = Nat.card t) :
    Set.BijOn f s t := by
  refine ⟨hmaps, hinj, ?_⟩
  have hbij := ((Set.MapsTo.restrict_inj hmaps).2 hinj).bijective_of_nat_card_le hcard.ge
  intro y hy
  obtain ⟨⟨x, hx⟩, hxy⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨x, hx, congrArg Subtype.val hxy⟩

theorem eq_of_map_eq_of_injOn {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    {H₁ H₂ : AddSubgroup G} (hf : Set.InjOn f (H₁ ⊔ H₂ : AddSubgroup G)) (h : H₁.map f = H₂.map f) :
    H₁ = H₂ := by
  have key : ∀ {A B : AddSubgroup G}, Set.InjOn f (A ⊔ B : AddSubgroup G) → A.map f = B.map f → A ≤ B := by
    intro A B hf h P hP
    have : f P ∈ B.map f := h ▸ ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, hQP⟩ := this
    have := hf (AddSubgroup.mem_sup_right hQ) (AddSubgroup.mem_sup_left hP) hQP
    rwa [← this]
  exact le_antisymm (key hf h) (key (sup_comm H₁ H₂ ▸ hf) h.symm)

end Groups

section Hahn

variable (L : Type u) [Field L]

def hahnO : ValuationSubring (HahnSeries ℚ L) where
  carrier := {x | 0 ≤ x.orderTop}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [HahnSeries.orderTop_mul]
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa only [Set.mem_setOf_eq, HahnSeries.orderTop_neg] using ha
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left; simp [hx]
    have hxi : x⁻¹ ≠ 0 := inv_ne_zero hx
    have h : x.orderTop + x⁻¹.orderTop = 0 := by
      rw [← HahnSeries.orderTop_mul, mul_inv_cancel₀ hx, HahnSeries.orderTop_one]
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx, ← HahnSeries.order_eq_orderTop_of_ne_zero hxi,
      ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h
    simp only [Set.mem_setOf_eq]
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx, ← HahnSeries.order_eq_orderTop_of_ne_zero hxi,
      ← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_le_coe]
    by_contra hcon
    simp only [not_or, not_le] at hcon
    linarith [hcon.1, hcon.2]

variable {L}

theorem mem_hahnO {x : HahnSeries ℚ L} : x ∈ hahnO L ↔ 0 ≤ x.orderTop := Iff.rfl

def sH : HahnSeries ℚ L := HahnSeries.single 1 1

theorem sH_mem : (sH : HahnSeries ℚ L) ∈ hahnO L := by
  rw [mem_hahnO, sH, HahnSeries.orderTop_single one_ne_zero]; exact zero_le_one

theorem C_mem (a : L) : (HahnSeries.C a : HahnSeries ℚ L) ∈ hahnO L := by
  rw [mem_hahnO]
  by_cases ha : a = 0
  · simp [ha]
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha]; exact le_rfl

theorem algebraMap_hahn (a : L) : algebraMap L (HahnSeries ℚ L) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  exact HahnSeries.ofPowerSeries_C a

theorem leadingCoeff_eq_coeff_order {x : HahnSeries ℚ L} (hx : x ≠ 0) :
    x.leadingCoeff = x.coeff x.order := by
  rw [HahnSeries.leadingCoeff_of_ne_zero hx]
  congr 1
  rw [WithTop.untop_eq_iff]
  exact (HahnSeries.order_eq_orderTop_of_ne_zero hx).symm

theorem coeff_zero_mul_of_nonneg {x y : HahnSeries ℚ L} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  rcases hx.lt_or_eq with h1 | h1
  · have hx0 : x.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop h1
    have hxy : (0 : WithTop ℚ) < (x * y).orderTop := by
      rw [HahnSeries.orderTop_mul]
      exact lt_of_lt_of_le h1 (le_add_of_nonneg_right hy)
    rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hxy, hx0, zero_mul]
  · rcases hy.lt_or_eq with h2 | h2
    · have hy0 : y.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop h2
      have hxy : (0 : WithTop ℚ) < (x * y).orderTop := by
        rw [HahnSeries.orderTop_mul]
        exact lt_of_lt_of_le h2 (le_add_of_nonneg_left hx)
      rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hxy, hy0, mul_zero]
    · have hx0 : x ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [← h1]; simp)
      have hy0 : y ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [← h2]; simp)
      have hordx : x.order = 0 := by
        have h : (x.order : WithTop ℚ) = 0 :=
          (HahnSeries.order_eq_orderTop_of_ne_zero hx0).trans h1.symm
        exact_mod_cast h
      have hordy : y.order = 0 := by
        have h : (y.order : WithTop ℚ) = 0 :=
          (HahnSeries.order_eq_orderTop_of_ne_zero hy0).trans h2.symm
        exact_mod_cast h
      have key := HahnSeries.coeff_mul_order_add_order x y
      rw [hordx, hordy, add_zero] at key
      rw [key, leadingCoeff_eq_coeff_order hx0, leadingCoeff_eq_coeff_order hy0, hordx, hordy]

variable (L) in

def rho : hahnO L →+* L where
  toFun x := (x : HahnSeries ℚ L).coeff 0
  map_one' := by
    rw [OneMemClass.coe_one, HahnSeries.coeff_one, if_pos rfl]
  map_mul' x y := by
    rw [Subring.coe_mul]
    exact coeff_zero_mul_of_nonneg (mem_hahnO.mp x.2) (mem_hahnO.mp y.2)
  map_zero' := by
    rw [ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  map_add' x y := by
    rw [Subring.coe_add, HahnSeries.coeff_add]

@[scoped simp] theorem rho_apply (x : hahnO L) : rho L x = (x : HahnSeries ℚ L).coeff 0 := rfl

theorem rho_C (a : L) : rho L ⟨HahnSeries.C a, C_mem a⟩ = a := by
  show (HahnSeries.C a : HahnSeries ℚ L).coeff 0 = a
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem rho_surjective : Function.Surjective (rho L) := fun a => ⟨_, rho_C a⟩

scoped instance isLocalHom_rho : IsLocalHom (rho L) := by
  refine ⟨fun x hx => ?_⟩
  have hx0 : (x : HahnSeries ℚ L).coeff 0 ≠ 0 := hx.ne_zero
  have hle : (x : HahnSeries ℚ L).orderTop ≤ 0 := HahnSeries.orderTop_le_of_coeff_ne_zero hx0
  have heq : (x : HahnSeries ℚ L).orderTop = 0 := le_antisymm hle (mem_hahnO.mp x.2)
  have hxne : (x : HahnSeries ℚ L) ≠ 0 := fun h => hx0 (by rw [h, HahnSeries.coeff_zero])
  have hinv : (x : HahnSeries ℚ L)⁻¹ ∈ hahnO L := by
    rw [mem_hahnO]
    have h : (x : HahnSeries ℚ L).orderTop + (x : HahnSeries ℚ L)⁻¹.orderTop = 0 := by
      rw [← HahnSeries.orderTop_mul, mul_inv_cancel₀ hxne, HahnSeries.orderTop_one]
    rw [heq, zero_add] at h
    exact h.ge
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hxne)⟩

variable (L) in

noncomputable def resEquiv : ResidueField (hahnO L) ≃+* L :=
  RingEquiv.ofBijective (ResidueField.lift (rho L))
    ⟨(ResidueField.lift (rho L)).injective, fun a => by
      obtain ⟨x, hx⟩ := rho_surjective (L := L) a
      exact ⟨residue _ x, by rw [ResidueField.lift_residue_apply, hx]⟩⟩

theorem resEquiv_residue (x : hahnO L) : resEquiv L (residue _ x) = rho L x :=
  ResidueField.lift_residue_apply _ _

theorem aeval_sH_injective : Function.Injective (aeval (R := L) (sH : HahnSeries ℚ L)) := by
  have h : (aeval (R := L) (sH : HahnSeries ℚ L)).toRingHom =
      (HahnSeries.ofPowerSeries ℚ L).comp (Polynomial.coeToPowerSeries.ringHom) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, algebraMap_hahn,
        RingHom.comp_apply]
      change HahnSeries.C a = HahnSeries.ofPowerSeries ℚ L ((C a : Polynomial L) : PowerSeries L)
      rw [Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply]
      change sH = HahnSeries.ofPowerSeries ℚ L ((X : Polynomial L) : PowerSeries L)
      rw [Polynomial.coe_X, HahnSeries.ofPowerSeries_X, sH]
  intro p q hpq
  have : (aeval (R := L) (sH : HahnSeries ℚ L)).toRingHom p = (aeval (R := L) (sH : HahnSeries ℚ L)).toRingHom q :=
    hpq
  rw [h] at this
  exact Polynomial.coe_injective L (HahnSeries.ofPowerSeries_injective this)

theorem exists_eq_C_of_isAlgebraic [IsAlgClosed L] {x : HahnSeries ℚ L} (hx : IsAlgebraic L x) :
    ∃ c : L, x = HahnSeries.C c := by
  have hint : _root_.IsIntegral L x := hx.isIntegral
  have hdeg : (minpoly L x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.degree_eq_one_iff.1 hdeg
  exact ⟨c, by rw [← hc, algebraMap_hahn]⟩

end Hahn

section Deform

variable {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic]

def Baux : WeierstrassCurve L := WeierstrassCurve.ofJ (E.j + 1)

scoped instance : (Baux E).IsElliptic := by unfold Baux; infer_instance

theorem Baux_j : (Baux E).j = E.j + 1 := by unfold Baux; exact ofJ_j _

def Epoly : WeierstrassCurve (Polynomial L) :=
  ⟨C E.a₁ + X * C ((Baux E).a₁ - E.a₁), C E.a₂ + X * C ((Baux E).a₂ - E.a₂),
    C E.a₃ + X * C ((Baux E).a₃ - E.a₃), C E.a₄ + X * C ((Baux E).a₄ - E.a₄),
    C E.a₆ + X * C ((Baux E).a₆ - E.a₆)⟩

theorem Epoly_eval_zero : (Epoly E).map (evalRingHom 0) = E := by
  ext <;> simp [Epoly]

theorem Epoly_eval_one : (Epoly E).map (evalRingHom 1) = Baux E := by
  ext <;> simp [Epoly]

def lineCoeff (a b : L) : hahnO L :=
  ⟨HahnSeries.C a + sH * HahnSeries.C (b - a), add_mem (C_mem a) (mul_mem sH_mem (C_mem _))⟩

theorem rho_lineCoeff (a b : L) : rho L (lineCoeff a b) = a := by
  rw [rho_apply, lineCoeff]
  change (HahnSeries.C a + sH * HahnSeries.C (b - a)).coeff 0 = a
  rw [HahnSeries.coeff_add, sH, HahnSeries.C_apply, HahnSeries.C_apply, HahnSeries.single_mul_single,
    HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne (by norm_num), add_zero]

theorem coe_lineCoeff (a b : L) :
    ((lineCoeff a b : hahnO L) : HahnSeries ℚ L) = aeval (R := L) sH (C a + X * C (b - a)) := by
  simp only [lineCoeff, map_add, map_mul, aeval_C, aeval_X, algebraMap_hahn]

def Wt : WeierstrassCurve (hahnO L) :=
  ⟨lineCoeff E.a₁ (Baux E).a₁, lineCoeff E.a₂ (Baux E).a₂, lineCoeff E.a₃ (Baux E).a₃,
    lineCoeff E.a₄ (Baux E).a₄, lineCoeff E.a₆ (Baux E).a₆⟩

theorem Wt_map_subtype : (Wt E).map (hahnO L).subtype = (Epoly E).map (aeval (R := L) sH).toRingHom := by
  ext <;> simp only [Wt, Epoly, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_lineCoeff]

theorem Wt_reduce : ((Wt E).map (residue (hahnO L))).map (resEquiv L).toRingHom = E := by
  ext <;> simp only [Wt, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, resEquiv_residue, rho_lineCoeff]

theorem Wt_goodReduction : ((Wt E).map (residue (hahnO L))).Δ ≠ 0 := by
  intro h
  have := congrArg (resEquiv L).toRingHom h
  rw [← map_Δ, Wt_reduce, map_zero] at this
  exact E.Δ'.ne_zero (by rw [coe_Δ']; exact this)

scoped instance : ((Wt E).map (hahnO L).subtype).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [map_Δ]
  intro h
  apply Wt_goodReduction E
  rw [map_Δ]
  have : (Wt E).Δ = 0 := Subtype.ext h
  rw [this, map_zero]

theorem c₄_pow_three_eq {F : Type*} [Field F] (V : WeierstrassCurve F) [V.IsElliptic] :
    V.c₄ ^ 3 = V.j * V.Δ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']
  field_simp [V.Δ'.ne_zero, show V.Δ ≠ 0 from by rw [← coe_Δ']; exact V.Δ'.ne_zero]

theorem transcendental_j_Wt [IsAlgClosed L] : Transcendental L ((Wt E).map (hahnO L).subtype).j := by
  intro halg
  obtain ⟨c, hc⟩ := exists_eq_C_of_isAlgebraic halg
  set V := (Wt E).map (hahnO L).subtype with hV
  have hc4 : V.c₄ = aeval (R := L) sH (Epoly E).c₄ := by
    rw [hV, Wt_map_subtype, map_c₄]; rfl
  have hΔ : V.Δ = aeval (R := L) sH (Epoly E).Δ := by
    rw [hV, Wt_map_subtype, map_Δ]; rfl

  have hid : (Epoly E).c₄ ^ 3 = C c * (Epoly E).Δ := by
    apply aeval_sH_injective
    rw [map_pow, map_mul, aeval_C, algebraMap_hahn, ← hc4, ← hΔ, c₄_pow_three_eq, hc]

  have h0 := congrArg (Polynomial.eval 0) hid
  have h1 := congrArg (Polynomial.eval 1) hid
  simp only [eval_pow, eval_mul, eval_C] at h0 h1
  rw [← coe_evalRingHom, ← map_c₄, ← map_Δ, Epoly_eval_zero, c₄_pow_three_eq] at h0
  rw [← coe_evalRingHom, ← map_c₄, ← map_Δ, Epoly_eval_one, c₄_pow_three_eq, Baux_j] at h1
  have hΔE : E.Δ ≠ 0 := by rw [← coe_Δ']; exact E.Δ'.ne_zero
  have hΔB : (Baux E).Δ ≠ 0 := by rw [← coe_Δ']; exact (Baux E).Δ'.ne_zero
  have e0 : E.j = c := mul_right_cancel₀ hΔE h0
  have e1 : E.j + 1 = c := mul_right_cancel₀ hΔB h1
  have : (1 : L) = 0 := by linear_combination e1 - e0
  exact one_ne_zero this

theorem Wt_map_rho : (Wt E).map (rho L) = E := by
  ext <;> simp only [Wt, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, rho_lineCoeff]

theorem j_Wt_mem : ((Wt E).map (hahnO L).subtype).j ∈ hahnO L := by
  set A := hahnO L
  set W := Wt E
  have hc : (W.map A.subtype).c₄ = ((W.c₄ : A) : HahnSeries ℚ L) := map_c₄ W A.subtype
  have hd : (W.map A.subtype).Δ = ((W.Δ : A) : HahnSeries ℚ L) := map_Δ W A.subtype
  have hcA : (W.map A.subtype).c₄ ^ 3 ∈ A := by rw [hc]; exact pow_mem (SetLike.coe_mem _) 3
  have hdu : (W.map A.subtype).Δ ∉ A.nonunits := by
    rw [hd, A.coe_mem_nonunits_iff_residue_eq_zero, ← map_Δ]; exact Wt_goodReduction E
  have hmem : (W.map A.subtype).c₄ ^ 3 / (W.map A.subtype).Δ ∈ A :=
    A.div_mem_of_mem_of_notMem_nonunits hcA hdu
  have hj : (W.map A.subtype).j = (W.map A.subtype).c₄ ^ 3 / (W.map A.subtype).Δ := by
    rw [eq_div_iff (A.ne_zero_of_notMem_nonunits hdu), ← c₄_pow_three_eq]
  rw [hj]; exact hmem

theorem rho_j_Wt : rho L ⟨((Wt E).map (hahnO L).subtype).j, j_Wt_mem E⟩ = E.j := by
  set A := hahnO L
  set W := Wt E
  have hc : (W.map A.subtype).c₄ = ((W.c₄ : A) : HahnSeries ℚ L) := map_c₄ W A.subtype
  have hd : (W.map A.subtype).Δ = ((W.Δ : A) : HahnSeries ℚ L) := map_Δ W A.subtype
  have hΔ0 : (W.map A.subtype).Δ ≠ 0 := by rw [← coe_Δ']; exact (W.map A.subtype).Δ'.ne_zero

  have key : (⟨(W.map A.subtype).j, j_Wt_mem E⟩ : A) * W.Δ = W.c₄ ^ 3 := by
    apply Subtype.ext
    push_cast
    rw [← hc, ← hd, ← c₄_pow_three_eq]
  have h2 := congrArg (rho L) key
  rw [map_mul, map_pow, ← map_Δ, ← map_c₄, Wt_map_rho, c₄_pow_three_eq] at h2
  have hΔE : E.Δ ≠ 0 := by rw [← coe_Δ']; exact E.Δ'.ne_zero
  exact mul_right_cancel₀ hΔE h2

theorem resEquiv_comp_residue : (resEquiv L).toRingHom.comp (residue (hahnO L)) = rho L :=
  RingHom.ext fun x => resEquiv_residue x

theorem Wt_reduce_map : ((Wt E).map (residue (hahnO L))).map (resEquiv L).toRingHom = E := by
  rw [WeierstrassCurve.map_map, resEquiv_comp_residue, Wt_map_rho]

end Deform

section Main

variable {L : Type u} [Field L] [DecidableEq L] [IsAlgClosed L]

theorem reduceHom_some {K : Type u} [Field K] [DecidableEq K] {A : ValuationSubring K}
    [DecidableEq (ResidueField A)] {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : K}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) :
    reduceHom hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) :=
  reducePoint_some_of_mem hΔ h hx

theorem split_residue (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (hN : (N : L) ≠ 0)
    (E : WeierstrassCurve L) [E.IsElliptic]
    [DecidableEq (HahnSeries ℚ L)] [DecidableEq (ResidueField (hahnO L))] :
    fib data.Φ (residue (hahnO L) ⟨_, j_Wt_mem E⟩) =
      ∏ᶠ H ∈ CycSub ((Wt E).map (residue (hahnO L))).toAffine.Point N,
        (X - C (((Wt E).map (residue (hahnO L))).cyclicQuotientJ H N)) := by
  haveI : IsAlgClosed (HahnSeries ℚ L) := HahnSeries.isAlgClosed_rat
  haveI : IsAlgClosed (ResidueField (hahnO L)) := IsAlgClosed.of_ringEquiv L _ (resEquiv L).symm
  have hΔ : ((Wt E).map (residue (hahnO L))).Δ ≠ 0 := Wt_goodReduction E
  haveI hVbell : ((Wt E).map (residue (hahnO L))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  have hNK : (N : HahnSeries ℚ L) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℚ) (R := L)) N]; exact HahnSeries.C_ne_zero hN
  have hNk : (N : ResidueField (hahnO L)) ≠ 0 := by
    intro h; apply hN
    have := congrArg (resEquiv L) h
    rwa [map_natCast, map_zero] at this
  have hN0 : N ≠ 0 := NeZero.ne N

  have hbij := bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j L N data (HahnSeries ℚ L)
    hNK ((Wt E).map (hahnO L).subtype) (transcendental_j_Wt E)
  have hTcard : Nat.card (CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N) = dedekindPsi N :=
    natCard_cycSub (k := HahnSeries ℚ L) (Ω := HahnSeries ℚ L) ((Wt E).map (hahnO L).subtype) hNK
  have hTfin : (CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N).Finite := by
    rw [← Set.finite_coe_iff]
    exact Nat.finite_of_card_ne_zero (by rw [hTcard]; exact (dedekindPsi_pos hN0).ne')
  have hsplitK : fib data.Φ ((Wt E).map (hahnO L).subtype).j =
      ∏ᶠ H ∈ CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N, (X - C (((Wt E).map (hahnO L).subtype).cyclicQuotientJ H N)) :=
    eq_finprod_of_bijOn (data.monic.map _) _ hbij (by rw [hTcard, data.monic.natDegree_map, data.natDegree_eq])

  have hR : ∀ H ∈ CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N,
      ∃ hmem : ((Wt E).map (hahnO L).subtype).cyclicQuotientJ H N ∈ hahnO L,
        residue (hahnO L) ⟨_, hmem⟩ = ((Wt E).map (residue (hahnO L))).cyclicQuotientJ (H.map (reduceHom hΔ)) N :=
    fun H hH => residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom hΔ hNk H hH.1 hH.2
  classical
  let cO : AddSubgroup ((Wt E).map (hahnO L).subtype).toAffine.Point → hahnO L := fun H =>
    if h : H ∈ CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N then ⟨_, (hR H h).fst⟩ else 0
  have hcO : ∀ H ∈ CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N,
      ((cO H : hahnO L) : HahnSeries ℚ L) = ((Wt E).map (hahnO L).subtype).cyclicQuotientJ H N ∧
        residue (hahnO L) (cO H) = ((Wt E).map (residue (hahnO L))).cyclicQuotientJ (H.map (reduceHom hΔ)) N := by
    intro H hH
    have h1 : cO H = ⟨_, (hR H hH).fst⟩ := dif_pos hH
    rw [h1]
    exact ⟨rfl, (hR H hH).snd⟩

  set TF := hTfin.toFinset with hTF
  have hmemTF : ∀ H, H ∈ TF ↔ H ∈ CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N := fun H => hTfin.mem_toFinset
  have hpq : fib data.Φ (⟨_, j_Wt_mem E⟩ : hahnO L) = ∏ H ∈ TF, (X - C (cO H)) := by
    apply Polynomial.map_injective (hahnO L).subtype (hahnO L).subtype_injective
    rw [fib_map, Polynomial.map_prod, ValuationSubring.coe_subtype, hsplitK,
      finprod_mem_eq_finite_toFinset_prod _ hTfin]
    refine Finset.prod_congr rfl fun H hH => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ValuationSubring.coe_subtype,
      (hcO H ((hmemTF H).1 hH)).1]

  have hred := congrArg (Polynomial.map (residue (hahnO L))) hpq
  rw [fib_map, Polynomial.map_prod] at hred
  rw [hred]
  have e2 : ∏ H ∈ TF, (X - C (cO H)).map (residue (hahnO L)) =
      ∏ H ∈ TF, (X - C (((Wt E).map (residue (hahnO L))).cyclicQuotientJ (H.map (reduceHom hΔ)) N)) := by
    refine Finset.prod_congr rfl fun H hH => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, (hcO H ((hmemTF H).1 hH)).2]
  rw [e2, ← finprod_mem_eq_finite_toFinset_prod
    (fun H => X - C (((Wt E).map (residue (hahnO L))).cyclicQuotientJ (H.map (reduceHom hΔ)) N)) hTfin]

  have hSkcard : Nat.card (CycSub ((Wt E).map (residue (hahnO L))).toAffine.Point N) = dedekindPsi N :=
    natCard_cycSub (k := ResidueField (hahnO L)) (Ω := ResidueField (hahnO L)) ((Wt E).map (residue (hahnO L))) hNk
  haveI : Finite (CycSub ((Wt E).map (residue (hahnO L))).toAffine.Point N) :=
    Nat.finite_of_card_ne_zero (by rw [hSkcard]; exact (dedekindPsi_pos hN0).ne')
  have hinjr : Set.InjOn (reduceHom hΔ) {P : ((Wt E).map (hahnO L).subtype).toAffine.Point | N • P = 0} :=
    fun P hP Q hQ h => eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ hNk hP hQ h
  have hbijr : Set.BijOn (fun H : AddSubgroup ((Wt E).map (hahnO L).subtype).toAffine.Point => H.map (reduceHom hΔ))
      (CycSub ((Wt E).map (hahnO L).subtype).toAffine.Point N) (CycSub ((Wt E).map (residue (hahnO L))).toAffine.Point N) := by
    refine bijOn_of_injOn_of_card_eq _ (fun H hH => ?_) (fun H₁ hH₁ H₂ hH₂ h => ?_) (by rw [hTcard, hSkcard])
    · exact map_mem_cycSub_of_injOn _ hH (hinjr.mono fun P hP => nsmul_eq_zero_of_mem_cycSub hH hP)
    · refine eq_of_map_eq_of_injOn (reduceHom hΔ) (hinjr.mono ?_) h
      intro P hP
      obtain ⟨P₁, hP₁, P₂, hP₂, rfl⟩ := AddSubgroup.mem_sup.1 hP
      show N • (P₁ + P₂) = 0
      rw [nsmul_add, nsmul_eq_zero_of_mem_cycSub hH₁ hP₁, nsmul_eq_zero_of_mem_cycSub hH₂ hP₂, add_zero]
  exact finprod_mem_eq_of_bijOn _ hbijr fun _ _ => rfl

theorem split_of_split_iso (N : ℕ) [NeZero N] (hN : (N : L) ≠ 0) (Φ : Polynomial (Polynomial ℤ))
    {k : Type u} [Field k] [DecidableEq k] [IsAlgClosed k] (e : k ≃+* L)
    (V : WeierstrassCurve k) [V.IsElliptic] (x : k)
    (h : fib Φ x = ∏ᶠ H ∈ CycSub V.toAffine.Point N, (X - C (V.cyclicQuotientJ H N))) :
    fib Φ (e x) =
      ∏ᶠ H ∈ CycSub (V.map e.toRingHom).toAffine.Point N, (X - C ((V.map e.toRingHom).cyclicQuotientJ H N)) := by
  letI : Algebra k L := e.toRingHom.toAlgebra
  let ε : k →ₐ[k] L := Algebra.ofId k L
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNk : (N : k) ≠ 0 := fun h0 => hN (by simpa using congrArg e h0)

  have hSk : Nat.card (CycSub V.toAffine.Point N) = dedekindPsi N := natCard_cycSub (k := k) (Ω := k) V hNk
  have hSkfin : (CycSub V.toAffine.Point N).Finite := by
    rw [← Set.finite_coe_iff]
    exact Nat.finite_of_card_ne_zero (by rw [hSk]; exact (dedekindPsi_pos hN0).ne')
  have hSL : Nat.card (CycSub (V.map e.toRingHom).toAffine.Point N) = dedekindPsi N :=
    natCard_cycSub (k := L) (Ω := L) (V.map e.toRingHom) hN
  haveI : Finite (CycSub (V.map e.toRingHom).toAffine.Point N) :=
    Nat.finite_of_card_ne_zero (by rw [hSL]; exact (dedekindPsi_pos hN0).ne')

  have h1 := congrArg (Polynomial.map e.toRingHom) h
  rw [fib_map] at h1
  rw [show e x = e.toRingHom x from rfl, h1]
  have h2 : Polynomial.map e.toRingHom (∏ᶠ H ∈ CycSub V.toAffine.Point N, (X - C (V.cyclicQuotientJ H N))) =
      ∏ᶠ H ∈ CycSub V.toAffine.Point N, (X - C (e (V.cyclicQuotientJ H N))) := by
    rw [finprod_mem_eq_finite_toFinset_prod _ hSkfin, Polynomial.map_prod,
      finprod_mem_eq_finite_toFinset_prod _ hSkfin]
    refine Finset.prod_congr rfl fun H _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [h2]

  have h3 : ∀ H : AddSubgroup V.toAffine.Point,
      e (V.cyclicQuotientJ H N) = (V.map e.toRingHom).cyclicQuotientJ (H.map (Affine.Point.map ε)) N := by
    intro H
    exact (V.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed (A := k) (B := L) ε H N).symm
  simp_rw [h3]

  have hinj : Function.Injective (Affine.Point.map (W' := V.toAffine) ε) := Affine.Point.map_injective ε
  refine finprod_mem_eq_of_bijOn (fun H : AddSubgroup V.toAffine.Point => H.map (Affine.Point.map ε))
    ?_ fun _ _ => rfl
  refine bijOn_of_injOn_of_card_eq _ (fun H hH => ?_) (fun H₁ _ H₂ _ hH => AddSubgroup.map_injective hinj hH)
    (by rw [hSk, hSL])
  exact map_mem_cycSub_of_injOn _ hH hinj.injOn

theorem main (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (hN : (N : L) ≠ 0)
    (E : WeierstrassCurve L) [E.IsElliptic] :
    fib data.Φ E.j = ∏ᶠ H ∈ CycSub E.toAffine.Point N, (X - C (E.cyclicQuotientJ H N)) := by
  letI : DecidableEq (HahnSeries ℚ L) := Classical.decEq _
  letI : DecidableEq (ResidueField (hahnO L)) := Classical.decEq _
  haveI : IsAlgClosed (ResidueField (hahnO L)) := IsAlgClosed.of_ringEquiv L _ (resEquiv L).symm
  haveI hVbell : ((Wt E).map (residue (hahnO L))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (Wt_goodReduction E)⟩
  have h := split_of_split_iso N hN data.Φ (resEquiv L) ((Wt E).map (residue (hahnO L))) _
    (split_residue N data hN E)
  have hE : ((Wt E).map (residue (hahnO L))).map (resEquiv L).toRingHom = E := Wt_reduce_map E
  have hj : resEquiv L (residue (hahnO L) ⟨_, j_Wt_mem E⟩) = E.j := by rw [resEquiv_residue, rho_j_Wt]
  rw [hj] at h
  rw [h]
  exact congrArg (fun V : WeierstrassCurve L =>
    ∏ᶠ H ∈ CycSub V.toAffine.Point N, (X - C (V.cyclicQuotientJ H N))) hE

end Main

end LangSplit
p2m_reactivate "P2MW.S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ.WeierstrassCurve.LangSplit"
end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ.WeierstrassCurve.LangSplit P2MW.S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ.WeierstrassCurve"

theorem solution (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] (hN : (N : L) ≠ 0)
    (E : WeierstrassCurve L) [E.IsElliptic] :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j) =
      ∏ᶠ H ∈ {H : AddSubgroup E.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N},
        (Polynomial.X - Polynomial.C (E.cyclicQuotientJ H N)) :=
  WeierstrassCurve.LangSplit.main N data hN E

end
end S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
end P2MW
export P2MW.S_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ (solution)

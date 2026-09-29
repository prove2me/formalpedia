-- Prove2me | solution 1 for ResidualGaloisRep.finrank_strictSelmer_adZero_le_card_taylorWilesPrimes_add_finrank_dualSelmer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/89d147c0-9bb7-59f5-8dab-d23146a41f21

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_groupCohomology_greenbergWiles_le_strict_relaxed_continuousH1S
import Theorems.Thm_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul
import Theorems.Thm_ResidualGaloisRep_det_complexConjugation_eq_neg_one_of_detIsCyclotomic
import Theorems.Thm_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
import Theorems.Thm_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
import Theorems.Thm_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finrank_strictSelmer_adZero_le_card_taylorWilesPrimes_add_finrank_dualSelmer
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup"
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup Rep.relationCarrier.instAddCommGroup NumberField.LevelArith.instCommGroupUnitsModPow groupCohomology.instMulDistribMulActionGaloisSUnits"
p2m_attr_erase "simp" "groupCohomology.cup_apply groupCohomology.cupCochain_apply groupCohomology.H1desc_H1π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.levelQuotientEquiv_mk groupCohomology.levelQuotientHom_mk Rep.toIntRepρ_apply_apply Rep.toIntRep_ρ Rep.toIntRepMap_hom_apply M4aHerbrand.AdeleBaseChange.classNorm_mk M4aHerbrand.AdeleBaseChange.coe_idelesMap_apply M4aHerbrand.AdeleBaseChange.classMap_mk M4aHerbrand.repHomResOfMulEquivariant_hom_apply M4aHerbrand.AdeleBaseChange.sClassNorm_mk M4aHerbrand.AdeleBaseChange.sClassMap_mk NumberField.SArchIdele.fibre_inl NumberField.SArchIdele.toSIdele_hom_apply_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inl NumberField.SArchIdele.fibre_inr Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g"
p2m_attr_erase "simp" "Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Rep.coe_dimShiftDownObjMap_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.frobeniusOnCoinvariants_mk groupCohomology.evalAtGen_apply Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply"

set_option autoImplicit false
open Polynomial CategoryTheory Module groupCohomology ExtCitation IntermediateField

noncomputable section

namespace P2mGWTW

abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

section Scalars

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k]

lemma two_ne_zero' (hp2 : p ≠ 2) : (2 : k) ≠ 0 := by
  intro h
  have h' : algebraMap (ZMod p) k 2 = 0 := by rw [map_ofNat]; exact h
  rw [map_eq_zero_iff _ (algebraMap (ZMod p) k).injective] at h'
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h'
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)

variable {W : Type} [AddCommGroup W] [Module k W] [Module (ZMod p) W]

lemma isScalarTower_zmod : IsScalarTower (ZMod p) k W := by
  constructor
  intro a b v
  have h1 : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X] (x : X), a • x = (a.val : ℕ) • x := by
    intro X _ _ x
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val x
  rw [h1 k b, h1 W (b • v), smul_assoc]

lemma finrank_restrictScalars_eq [IsScalarTower (ZMod p) k W] (N : Submodule k W) :
    finrank (ZMod p) ↥(N.restrictScalars (ZMod p)) = finrank (ZMod p) k * finrank k ↥N := by
  change finrank (ZMod p) ↥N = _
  rw [Module.finrank_mul_finrank]

end Scalars

section AdZero

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime]
variable {ρbar : ResidualGaloisRep k}
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  {ρ₀ : Representation (ZMod p) Γ (LinearMap.ker (LinearMap.trace k ρbar.V))}

lemma rho0_eq_one (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ} (hg : ρbar.ρ g = 1) :
    ρ₀ g = 1 := by
  have hg' : ρbar.ρ g⁻¹ = 1 := by
    have : ρbar.ρ g⁻¹ * ρbar.ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rwa [hg, mul_one] at this
  apply LinearMap.ext
  intro v
  rw [hρ₀ g v, Module.End.one_apply]
  apply Subtype.ext
  rw [ResidualGaloisRep.adZeroRep_apply_coe, hg, hg', one_mul, mul_one]

lemma hsm₀ (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) :
    ∀ m : (Rep.of ρ₀), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, (Rep.of ρ₀).ρ s m = m := by
  intro m
  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  refine ⟨L, hLfd, fun s hs => ?_⟩
  have hρs : ρbar.ρ s = 1 := hL s ((mem_fixingSubgroup_iff (K := L) s).mp hs)
  change ρ₀ s m = m
  rw [rho0_eq_one hρ₀ hρs, Module.End.one_apply]

lemma hMur₀ (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) (S' : Finset Nat.Primes)
    (hur : ∀ q : Nat.Primes, q ∉ S' → ρbar.IsUnramifiedAt q) :
    ∀ q : Nat.Primes, q ∉ S' → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (Rep.of ρ₀).ρ g = 1 := by
  intro q hq A hA g hg
  change ρ₀ g = 1
  exact rho0_eq_one hρ₀ (hur q hq A hA g hg)

lemma invariants_eq_bot (h2 : (2 : k) ≠ 0) (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) :
    (Rep.of ρ₀).ρ.invariants = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Representation.mem_invariants] at hv
  set Y : Module.End k ρbar.V := (v : Module.End k ρbar.V) with hYdef
  have hY : ∀ σ, Y * ρbar.ρ σ = (((1 : Γ →* kˣ) σ : kˣ) : k) • (ρbar.ρ σ * Y) := by
    intro σ
    have hσ := hv σ
    change ρ₀ σ v = v at hσ
    rw [hρ₀] at hσ
    have hσ' := congrArg (fun w : LinearMap.ker (LinearMap.trace k ρbar.V) => (w : Module.End k ρbar.V)) hσ
    simp only [ResidualGaloisRep.adZeroRep_apply_coe] at hσ'

    have : Y * ρbar.ρ σ = ρbar.ρ σ * Y := by
      calc Y * ρbar.ρ σ = (ρbar.ρ σ * Y * ρbar.ρ σ⁻¹) * ρbar.ρ σ := by rw [hσ']
        _ = ρbar.ρ σ * Y := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    simpa using this
  obtain ⟨c, hc, -⟩ :=
    ResidualGaloisRep.exists_eq_smul_one_of_forall_mul_eq_smul_mul h2 ρbar habs hTW 1 Y hY
  have htr : LinearMap.trace k ρbar.V Y = 0 := v.2
  rw [hc, map_smul, LinearMap.trace_one, ρbar.finrank_eq, smul_eq_mul] at htr
  have hc0 : c = 0 := by
    have : c * 2 = 0 := by exact_mod_cast htr
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h h2
  apply Subtype.ext
  change Y = 0
  rw [hc, hc0, zero_smul]

end AdZero

section TWPrime

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k]
variable {ρbar : ResidualGaloisRep k}
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  [IsScalarTower (ZMod p) k (LinearMap.ker (LinearMap.trace k ρbar.V))]
  {ρ₀ : Representation (ZMod p) Γ (LinearMap.ker (LinearMap.trace k ρbar.V))}

lemma invariants_res_eq (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    {H : Type} [Group H] (l : H →* Γ) :
    (Rep.res l (Rep.of ρ₀)).ρ.invariants =
      ((Rep.res l ρbar.adZero).ρ.invariants).restrictScalars (ZMod p) := by
  ext v
  rw [Submodule.restrictScalars_mem, Representation.mem_invariants, Representation.mem_invariants]
  constructor
  · intro h g
    have := h g
    change ρ₀ (l g) v = v at this
    change ρbar.adZeroRep (l g) v = v
    rw [← hρ₀]; exact this
  · intro h g
    have := h g
    change ρbar.adZeroRep (l g) v = v at this
    change ρ₀ (l g) v = v
    rw [hρ₀]; exact this

lemma adZeroRep_inv_apply_eq_iff (σ : Γ) (v : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ρbar.adZeroRep σ⁻¹ v = v ↔ ρbar.adZeroRep σ v = v := by
  constructor
  · intro h
    have := congrArg (ρbar.adZeroRep σ) h
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm
  · intro h
    have := congrArg (ρbar.adZeroRep σ⁻¹) h
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

lemma finrank_dualTwist_invariants_le [Finite k] (hp2 : p ≠ 2)
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (q : Nat.Primes) (hqp : (q : ℕ) ≠ p) (hq1 : (q : ℕ) ≡ 1 [MOD p])
    (hreg : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ φ : Γ, P.IsFrobeniusAt φ q →
        ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) :
    finrank (ZMod p)
        ↥((Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).dualTwist
            ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants
      ≤ finrank (ZMod p) k := by
  classical
  haveI : Finite (LinearMap.ker (LinearMap.trace k ρbar.V)) := Module.finite_of_finite k
  haveI : Module.Finite (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V)) := Module.Finite.of_finite

  obtain ⟨φl, hφl⟩ := ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal q
  set φ : Γ := primeLocalToGlobal q φl with hφdef
  have hχ : ((cycloChar p φ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [hφdef, ExtCitation.coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt p q hqp hφl]
    have := (ZMod.natCast_eq_natCast_iff (q : ℕ) 1 p).2 hq1
    rw [Nat.cast_one] at this
    exact this
  obtain ⟨α, β, hαβ, hchar⟩ :=
    hreg (primeLocalPlace q) (ExtCitation.liesOverPrime_primeLocalPlace q) φ hφl

  set A : LinearMap.ker (LinearMap.trace k ρbar.V) →ₗ[ZMod p]
      LinearMap.ker (LinearMap.trace k ρbar.V) := ρ₀ φ⁻¹ with hA
  have hle : ((Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).dualTwist
        ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants ≤
      (LinearMap.range (A - 1)).dualAnnihilator := by
    intro F hF
    rw [Representation.mem_invariants] at hF
    have h := hF φl
    rw [Rep.dualTwist_ρ_apply] at h
    have hcomp : ((cycloChar p).comp (primeLocalToGlobal q)) φl = cycloChar p φ := rfl
    rw [hcomp] at h
    have hunit : (cycloChar p φ : (ZMod p)ˣ) = 1 := Units.ext hχ
    rw [hunit, Units.val_one, one_smul] at h
    have hres : (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).ρ φl⁻¹ = A := by
      rw [hA]; change ρ₀ (primeLocalToGlobal q φl⁻¹) = _; rw [map_inv]
    rw [hres] at h
    rw [Submodule.mem_dualAnnihilator]
    rintro w ⟨u, rfl⟩
    change F ((A - 1) u) = 0
    rw [LinearMap.sub_apply, map_sub, Module.End.one_apply]
    have := LinearMap.congr_fun h u
    rw [LinearMap.comp_apply] at this
    change F (A u) = F u at this
    rw [this, sub_self]

  have hann : finrank (ZMod p) ↥(LinearMap.range (A - 1)).dualAnnihilator =
      finrank (ZMod p) ↥(LinearMap.ker (A - 1)) := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range (A - 1))
    have h2 := LinearMap.finrank_range_add_finrank_ker (A - 1)
    omega

  have hker : LinearMap.ker (A - 1) =
      (LinearMap.ker (ρbar.adZeroRep φ - 1)).restrictScalars (ZMod p) := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      Submodule.restrictScalars_mem]
    rw [hA, hρ₀]
    exact adZeroRep_inv_apply_eq_iff φ v
  have h2 : (2 : k) ≠ 0 := two_ne_zero' hp2
  have hone : finrank k ↥(LinearMap.ker (ρbar.adZeroRep φ - 1)) = 1 :=
    ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq h2 ρbar φ hαβ hchar
  calc finrank (ZMod p) _ ≤ finrank (ZMod p) ↥(LinearMap.range (A - 1)).dualAnnihilator :=
        Submodule.finrank_mono hle
    _ = finrank (ZMod p) k := by
        rw [hann, hker, finrank_restrictScalars_eq, hone, mul_one]

lemma finrank_continuousH1_le [Finite k] (hp2 : p ≠ 2)
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (q : Nat.Primes) (hqp : (q : ℕ) ≠ p) (hq1 : (q : ℕ) ≡ 1 [MOD p])
    (hreg : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ φ : Γ, P.IsFrobeniusAt φ q →
        ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) :
    finrank (ZMod p)
        ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)))
      ≤ finrank (ZMod p) (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).ρ.invariants
        + finrank (ZMod p) k := by
  classical
  by_cases hfin : FiniteDimensional (ZMod p)
      ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)))
  · haveI := hfin
    haveI : Finite (LinearMap.ker (LinearMap.trace k ρbar.V)) := Module.finite_of_finite k
    haveI : FiniteDimensional (ZMod p) (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)) := by
      change Module.Finite (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))
      exact Module.Finite.of_finite
    have hsmN : ∀ m : (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)),
        ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup →
            (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).ρ s m = m := by
      intro m
      obtain ⟨F, hF, h⟩ := hsm₀ hρ₀ m
      exact ⟨F, hF, fun s hs => h _ hs⟩
    have hb := groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist q hqp
      (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)) hsmN
      (continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)))
      (fun x => by rw [mem_continuousH1_iff]; rfl)
    have hd := finrank_dualTwist_invariants_le hp2 hρ₀ q hqp hq1 hreg
    omega
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

end TWPrime

theorem main
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [Algebra (ZMod p) k]
    (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (S Q : Finset Nat.Primes) (hpS : pPrime p ∈ S) (hSQ : Disjoint S Q)
    (hur : ∀ q : Nat.Primes, q ∉ S → ρbar.IsUnramifiedAt q)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≡ 1 [MOD p] ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) :
    Module.finrank (ZMod p) ↥(continuousH1S (S ∪ Q) (Rep.of ρ₀) ⊓
        ⨅ q ∈ S, LinearMap.ker (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀))) 1).hom)
      + Module.finrank (ZMod p) k
      + Module.finrank (ZMod p) k *
          ∑ q ∈ S, Module.finrank k (Rep.res (primeLocalToGlobal q) ρbar.adZero).ρ.invariants
    ≤ Module.finrank (ZMod p) k * Q.card
      + Module.finrank (ZMod p) ↥(continuousH1S (S ∪ Q) ((Rep.of ρ₀).dualTwist (cycloChar p)) ⊓
          ⨅ q ∈ Q, LinearMap.ker (groupCohomology.map (primeLocalToGlobal q)
            (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom) := by
  classical
  haveI : IsScalarTower (ZMod p) k (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
    isScalarTower_zmod (k := k) (p := p) (W := LinearMap.ker (LinearMap.trace k ρbar.V))
  haveI : Finite (LinearMap.ker (LinearMap.trace k ρbar.V)) := Module.finite_of_finite k
  haveI : FiniteDimensional (ZMod p) (Rep.of ρ₀) := by
    change Module.Finite (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))
    exact Module.Finite.of_finite
  have h2 : (2 : k) ≠ 0 := two_ne_zero' hp2
  set f := Module.finrank (ZMod p) k with hf

  have hMur : ∀ q : Nat.Primes, q ∉ S ∪ Q → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (Rep.of ρ₀).ρ g = 1 :=
    fun q hq => hMur₀ hρ₀ (S ∪ Q) (fun q' hq' => hur q' fun h => hq' (Finset.mem_union_left _ h)) q hq
  have hGW := groupCohomology.greenbergWiles_le_strict_relaxed_continuousH1S hp2 S Q hpS hSQ
    (Rep.of ρ₀) (hsm₀ hρ₀) hMur

  have hT : Module.finrank (ZMod p) ↥(Rep.of ρ₀).ρ.invariants = 0 := by
    rw [invariants_eq_bot h2 habs hTW hρ₀, finrank_bot]

  have hE : Module.finrank (ZMod p) ↥(Rep.res archimedeanLoc (Rep.of ρ₀)).ρ.invariants = f := by
    rw [invariants_res_eq hρ₀ archimedeanLoc, finrank_restrictScalars_eq]
    have hc : LinearMap.det (ρbar.ρ complexConjugation) = -1 :=
      ResidualGaloisRep.det_complexConjugation_eq_neg_one_of_detIsCyclotomic p ρbar hdet
    have h1 := ResidualGaloisRep.finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one h2 ρbar
      complexConjugation complexConjugation_mul_self hc
    change f * Module.finrank k
      ↥(Rep.res (Subgroup.zpowers complexConjugation).subtype ρbar.adZero).ρ.invariants = f
    rw [h1, mul_one]

  have hSterm : ∑ q ∈ S, Module.finrank (ZMod p) ↥(Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).ρ.invariants
      = f * ∑ q ∈ S, Module.finrank k ↥(Rep.res (primeLocalToGlobal q) ρbar.adZero).ρ.invariants := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [invariants_res_eq hρ₀ (primeLocalToGlobal q), finrank_restrictScalars_eq]

  have hQterm : ∑ q ∈ Q, Module.finrank (ZMod p)
        ↥(continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)))
      ≤ ∑ q ∈ Q, Module.finrank (ZMod p) ↥(Rep.res (primeLocalToGlobal q) (Rep.of ρ₀)).ρ.invariants
        + f * Q.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, mul_one, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    have hqp : (q : ℕ) ≠ p := by
      intro h
      have : q = pPrime p := Subtype.ext h
      exact Finset.disjoint_left.1 hSQ hpS (this ▸ hq)
    exact finrank_continuousH1_le hp2 hρ₀ q hqp (hQ q hq).1 (hQ q hq).2

  rw [Finset.sum_union hSQ, hT, hE, hSterm] at hGW
  set A := f * ∑ q ∈ S, Module.finrank k ↥(Rep.res (primeLocalToGlobal q) ρbar.adZero).ρ.invariants
  set B := f * Q.card
  omega

end P2mGWTW

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [Algebra (ZMod p) k]
    (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (S Q : Finset Nat.Primes) (hpS : pPrime p ∈ S) (hSQ : Disjoint S Q)
    (hur : ∀ q : Nat.Primes, q ∉ S → ρbar.IsUnramifiedAt q)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≡ 1 [MOD p] ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) :
    Module.finrank (ZMod p) ↥(continuousH1S (S ∪ Q) (Rep.of ρ₀) ⊓
        ⨅ q ∈ S, LinearMap.ker (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) (Rep.of ρ₀))) 1).hom)
      + Module.finrank (ZMod p) k
      + Module.finrank (ZMod p) k *
          ∑ q ∈ S, Module.finrank k (Rep.res (primeLocalToGlobal q) ρbar.adZero).ρ.invariants
    ≤ Module.finrank (ZMod p) k * Q.card
      + Module.finrank (ZMod p) ↥(continuousH1S (S ∪ Q) ((Rep.of ρ₀).dualTwist (cycloChar p)) ⊓
          ⨅ q ∈ Q, LinearMap.ker (groupCohomology.map (primeLocalToGlobal q)
            (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom) :=
  P2mGWTW.main p hp2 ρbar habs hdet hTW ρ₀ hρ₀ S Q hpS hSQ hur hQ

end

end S_ResidualGaloisRep_finrank_strictSelmer_adZero_le_card_taylorWilesPrimes_add_finrank_dualSelmer
end P2MW
export P2MW.S_ResidualGaloisRep_finrank_strictSelmer_adZero_le_card_taylorWilesPrimes_add_finrank_dualSelmer (solution)

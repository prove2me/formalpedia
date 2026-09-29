-- Prove2me | solution 1 for ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bc42f51f-65ef-5e79-accd-54ec553a6f53

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
import Theorems.Thm_ResidualGaloisRep_finrank_strictSelmer_adZero_le_card_taylorWilesPrimes_add_finrank_dualSelmer
import Theorems.Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
import Theorems.Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
import Theorems.Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt
import Theorems.Thm_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt
import Theorems.Thm_groupCohomology_exists_bijective_H1_map_of_restrictScalars
import Theorems.Thm_groupCohomology_eq_continuousH1S_of_forall_mem_iff
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup Rep.relationCarrier.instAddCommGroup NumberField.LevelArith.instCommGroupUnitsModPow groupCohomology.instMulDistribMulActionGaloisSUnits GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra Deformation.HondaSystem.instAddCommGroupSelfExt Deformation.HondaSystem.instModuleSelfExt Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup instIsScalarTowerTensorProduct_definitions CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg"
p2m_attr_erase "instance" "MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal Deformation.HondaSystem.SplitCoordinates.instHopfGc Deformation.HondaSystem.SplitCoordinates.instCommRingGe Deformation.HondaSystem.SplitCoordinates.instCommRingGc Deformation.HondaSystem.SplitCoordinates.instCommRingEt Deformation.HondaSystem.SplitCoordinates.instHopfGe Deformation.HondaSystem.SplitCoordinates.instHopfEt Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec TaylorWiles.CyclotomicLevelStructure.mk.sizeOf_spec TaylorWiles.CyclotomicLevelStructure.mk.injEq ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe groupCohomology.cup_apply groupCohomology.cupCochain_apply groupCohomology.H1desc_H1π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply"
p2m_attr_erase "simp" "SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.levelQuotientEquiv_mk groupCohomology.levelQuotientHom_mk Rep.toIntRepρ_apply_apply Rep.toIntRep_ρ Rep.toIntRepMap_hom_apply M4aHerbrand.AdeleBaseChange.classNorm_mk M4aHerbrand.AdeleBaseChange.coe_idelesMap_apply M4aHerbrand.AdeleBaseChange.classMap_mk M4aHerbrand.repHomResOfMulEquivariant_hom_apply M4aHerbrand.AdeleBaseChange.sClassNorm_mk M4aHerbrand.AdeleBaseChange.sClassMap_mk NumberField.SArchIdele.fibre_inl NumberField.SArchIdele.toSIdele_hom_apply_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inr NumberField.SArchIdele.toSIdele_hom_apply_inl_inl NumberField.SArchIdele.fibre_inr Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂"
p2m_attr_erase "simp" "Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Rep.coe_dimShiftDownObjMap_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.frobeniusOnCoinvariants_mk groupCohomology.evalAtGen_apply Rep.quotientRightTranslation_hom_single Rep.quotientRightTranslationTwist_hom_apply groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply ResidualGaloisRep.adZeroEquivTraceZero_apply_coe TaylorWiles.mem_traceZero_iff TaylorWiles.adAction_apply GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE"
p2m_attr_erase "simp" "Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply"
p2m_attr_erase "simp" "HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries"
p2m_attr_erase "simp" "MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto Deformation.HondaSystem.SplitCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "Deformation.HondaSystem.SplitCoordinates.mk.injEq Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.PLoc.map_algebraMap Deformation.PLoc.map_invPow Deformation.UnipotentWittCovector.wUp_of Deformation.UnipotentWittCovector.wHom_apply Deformation.UnipotentWittCovector.wLevel_succ_truncate Deformation.PLoc.mapLinear_apply"

set_option autoImplicit false

open Polynomial IsLocalRing groupCohomology TrivSqZeroExt CategoryTheory Module ExtCitation

noncomputable section

namespace P2mK4NS

abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

section Adm

variable {K : Type} [CommRing K] (M : Rep K Γ)

def admSub (S₀ : Finset Nat.Primes) : Submodule K (H1 M) where
  carrier := {x | ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
      (∀ q : Nat.Primes, q ∉ S₀ → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
      H1π M c = x}
  zero_mem' := ⟨0, IsLocallyConstant.const (0 : M), fun q _ A _ =>
    ⟨0, fun g _ => by change (0 : M) = _; simp⟩, map_zero _⟩
  add_mem' := by
    rintro x y ⟨c, hc, hcq, rfl⟩ ⟨d, hd, hdq, rfl⟩
    refine ⟨c + d, ?_, fun q hq A hA => ?_, map_add _ _ _⟩
    · have : ⇑(c + d) = ⇑c + ⇑d := rfl
      rw [this]
      exact hc.add hd
    · obtain ⟨m, hm⟩ := hcq q hq A hA
      obtain ⟨m', hm'⟩ := hdq q hq A hA
      refine ⟨m + m', fun g hg => ?_⟩
      have : (c + d) g = c g + d g := rfl
      rw [this, hm g hg, hm' g hg, map_add]
      abel
  smul_mem' := by
    rintro a x ⟨c, hc, hcq, rfl⟩
    refine ⟨a • c, ?_, fun q hq A hA => ?_, map_smul _ _ _⟩
    · have : ⇑(a • c) = (fun m : M => a • m) ∘ ⇑c := rfl
      rw [this]
      exact hc.comp _
    · obtain ⟨m, hm⟩ := hcq q hq A hA
      refine ⟨a • m, fun g hg => ?_⟩
      have : (a • c) g = a • c g := rfl
      rw [this, hm g hg, map_smul, smul_sub]

lemma mem_admSub_iff (S₀ : Finset Nat.Primes) (x : H1 M) :
    x ∈ admSub M S₀ ↔ ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
      (∀ q : Nat.Primes, q ∉ S₀ → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
      H1π M c = x := Iff.rfl

theorem H1π_surj {G : Type} [Group G] (B : Rep K G) (x : H1 B) :
    ∃ c : cocycles₁ B, H1π B c = x :=
  H1_induction_on x (fun c => ⟨c, rfl⟩)

private abbrev _root_.P2mK4NS.res {H : Type} [Group H] (l : H →* Γ) : H1 M →ₗ[K] H1 (Rep.res l M) :=
  (groupCohomology.map l (𝟙 (Rep.res l M)) 1).hom

p2m_export "P2mK4NS" "res"

lemma res_H1π_eq_zero_iff {H : Type} [Group H] (l : H →* Γ) (c : cocycles₁ M) :
    res M l (H1π M c) = 0 ↔ ∃ m : M, ∀ h : H, c (l h) = M.ρ (l h) m - m := by
  have hres : res M l (H1π M c) = H1π (Rep.res l M) (mapCocycles₁ l (𝟙 (Rep.res l M)) c) := by
    erw [H1π_comp_map_apply]
  rw [hres, H1π_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun h => ?_⟩
    have := congrFun hm h
    rw [d₀₁_hom_apply] at this
    exact this.symm
  · rintro ⟨m, hm⟩
    refine ⟨m, funext fun h => ?_⟩
    rw [d₀₁_hom_apply]
    exact (hm h).symm

end Adm

section Scalars

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k]

variable {W : Type} [AddCommGroup W] [Module k W] [Module (ZMod p) W]

lemma isScalarTower_zmod : IsScalarTower (ZMod p) k W := by
  constructor
  intro a b v
  have h1 : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X] (x : X), a • x = (a.val : ℕ) • x := by
    intro X _ _ x
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val x
  rw [h1 k b, h1 W (b • v), smul_assoc]

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
  have hρs : ρbar.ρ s = 1 := hL s ((IntermediateField.mem_fixingSubgroup_iff (K := L) s).mp hs)
  change ρ₀ s m = m
  rw [rho0_eq_one hρ₀ hρs, Module.End.one_apply]

lemma hMur₀ (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) (S' : Finset Nat.Primes)
    (hur : ∀ q : Nat.Primes, q ∉ S' → ρbar.IsUnramifiedAt q) :
    ∀ q : Nat.Primes, q ∉ S' → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (Rep.of ρ₀).ρ g = 1 := by
  intro q hq A hA g hg
  change ρ₀ g = 1
  exact rho0_eq_one hρ₀ (hur q hq A hA g hg)

end AdZero

section Core

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
variable (ρbar : ResidualGaloisRep k)
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  [IsScalarTower (ZMod p) k (LinearMap.ker (LinearMap.trace k ρbar.V))]
  (ρ₀ : Representation (ZMod p) Γ (LinearMap.ker (LinearMap.trace k ρbar.V)))
  (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)

local notation "M" => ResidualGaloisRep.adZero ρbar
local notation "M₀" => Rep.of ρ₀
local notation "loc" => primeLocalToGlobal

def IsTangentClass (𝒞 : GaloisRepAdic (DualNumber k) → Prop) (x : H1 M) : Prop :=
  ∃ c : cocycles₁ M, H1π M c = x ∧
    ∃ ρA : GaloisRepAdic (DualNumber k), 𝒞 ρA ∧
    ∃ ρd : Γ →* (DualNumber (Module.End k ρbar.V))ˣ,
      IsDualLift ρbar.ρ.toHomUnits ρd ∧
      (∀ σ, ((c : Γ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
        dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
      ∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
        ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
          Matrix.dualNumberEquiv.symm
            ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
              LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩

def LocalBound (𝒞 : GaloisRepAdic (DualNumber k) → Prop) (q : Nat.Primes) (d : ℕ)
    (L : Submodule k (H1 (Rep.res (loc q) M))) : Prop :=
  FiniteDimensional k L ∧ Module.finrank k L ≤ d ∧
    ∀ (ρA : GaloisRepAdic (DualNumber k)), 𝒞 ρA →
      ∀ ρd : Γ →* (DualNumber (Module.End k ρbar.V))ˣ,
        IsDualLift ρbar.ρ.toHomUnits ρd →
        (∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
          ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
            Matrix.dualNumberEquiv.symm
              ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
                LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) →
        ∀ c : cocycles₁ M,
          (∀ σ, ((c : Γ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
            dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) →
          res M (loc q) (H1π M c) ∈ L

variable {p ρbar}

lemma isTangentClass_mem_admSub {𝒞 : GaloisRepAdic (DualNumber k) → Prop} (S₀ : Finset Nat.Primes)
    (h𝒞ur : ∀ ρA, 𝒞 ρA → ∀ q : Nat.Primes, q ∉ S₀ → ρA.IsUnramifiedAt q)
    {x : H1 M} (hx : IsTangentClass ρbar 𝒞 x) : x ∈ admSub M S₀ := by
  obtain ⟨c, hcx, ρA, hA, ρd, hd, hc, b, bbar, hfr⟩ := hx
  obtain ⟨hlc, -, hur⟩ :=
    GaloisRepAdic.isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt ρbar ρA ρd hd b bbar hfr
  refine ⟨c, ?_, fun q hq A' hA' => ⟨0, fun g hg => ?_⟩, hcx⟩
  ·
    have hcomp : (Subtype.val ∘ (c : Γ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V)))) =
        dualLiftToCochain ρbar.ρ.toHomUnits ρd := funext hc
    have : IsLocallyConstant (Subtype.val ∘ (c : Γ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V)))) := by
      rw [hcomp]; exact hlc
    exact IsLocallyConstant.desc _ Subtype.val this Subtype.val_injective
  · rw [map_zero, sub_zero]
    apply Subtype.ext
    change ((c : Γ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) g : Module.End k ρbar.V) = _
    rw [hc]
    exact hur q (h𝒞ur ρA hA q hq) A' hA' g hg

variable (p ρbar)

include hρ₀ in

theorem finrank_span_le [Finite k] (hp2 : p ≠ 2)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (S' Q : Finset Nat.Primes) (hpS : pPrime p ∈ S') (hSQ : Disjoint S' Q)
    (hur : ∀ q : Nat.Primes, q ∉ S' → ρbar.IsUnramifiedAt q)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≡ 1 [MOD p] ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β))
    (hkill : ∀ x ∈ continuousH1S (S' ∪ Q) ((M₀).dualTwist (cycloChar p)),
      (∀ q ∈ Q, (groupCohomology.map (loc q)
        (𝟙 (Rep.res (loc q) ((M₀).dualTwist (cycloChar p)))) 1).hom x = 0) → x = 0)
    (𝒞 : GaloisRepAdic (DualNumber k) → Prop)
    (h𝒞ur : ∀ ρA, 𝒞 ρA → ∀ q : Nat.Primes, q ∉ S' ∪ Q → ρA.IsUnramifiedAt q)
    (Lp : Submodule k (H1 (Rep.res (loc (pPrime p)) M)))
    (hLp : LocalBound ρbar 𝒞 (pPrime p)
      (Module.finrank k (Rep.res (loc (pPrime p)) M).ρ.invariants + 1) Lp)
    (Lℓ : ∀ ℓ : ↥(S'.erase (pPrime p)), Submodule k (H1 (Rep.res (loc (ℓ : Nat.Primes)) M)))
    (hLℓ : ∀ ℓ : ↥(S'.erase (pPrime p)), LocalBound ρbar 𝒞 ℓ
      (Module.finrank k (Rep.res (loc (ℓ : Nat.Primes)) M).ρ.invariants) (Lℓ ℓ)) :
    Module.finrank k ↥(Submodule.span k {x : H1 M | IsTangentClass ρbar 𝒞 x}) ≤ Q.card := by
  classical
  haveI : Finite (LinearMap.ker (LinearMap.trace k ρbar.V)) := Module.finite_of_finite k
  haveI : FiniteDimensional (ZMod p) (M₀) := by
    change Module.Finite (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))
    exact Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod p) k := Module.Finite.of_finite
  haveI hLpfd : FiniteDimensional k Lp := hLp.1
  haveI hLℓfd : ∀ ℓ, FiniteDimensional k (Lℓ ℓ) := fun ℓ => (hLℓ ℓ).1
  set f : ℕ := Module.finrank (ZMod p) k with hfdef
  have hfpos : 0 < f := Module.finrank_pos
  set Y : Submodule k (H1 M) := Submodule.span k {x : H1 M | IsTangentClass ρbar 𝒞 x} with hYdef

  set Sel : Submodule (ZMod p) (H1 (M₀)) := continuousH1S (S' ∪ Q) (M₀) ⊓
      ⨅ q ∈ S', LinearMap.ker (groupCohomology.map (loc q) (𝟙 (Rep.res (loc q) (M₀))) 1).hom
    with hSeldef
  haveI hSelfd : FiniteDimensional (ZMod p) Sel := by
    haveI := groupCohomology.finiteDimensional_continuousH1S (S' ∪ Q) (M₀) (hsm₀ hρ₀)
    exact Submodule.finiteDimensional_of_le inf_le_left

  have hYadm : Y ≤ admSub M (S' ∪ Q) :=
    Submodule.span_le.2 fun x hx => isTangentClass_mem_admSub (S' ∪ Q) h𝒞ur hx

  have hYp : ∀ y ∈ Y, res M (loc (pPrime p)) y ∈ Lp := by
    have : Y ≤ Lp.comap (res M (loc (pPrime p))) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨c, hcx, ρA, hA, ρd, hd, hc, b, bbar, hfr⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hcx]
      exact hLp.2.2 ρA hA ρd hd ⟨b, bbar, hfr⟩ c hc
    exact fun y hy => this hy
  have hYℓ : ∀ ℓ : ↥(S'.erase (pPrime p)), ∀ y ∈ Y, res M (loc (ℓ : Nat.Primes)) y ∈ Lℓ ℓ := by
    intro ℓ
    have : Y ≤ (Lℓ ℓ).comap (res M (loc (ℓ : Nat.Primes))) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨c, hcx, ρA, hA, ρd, hd, hc, b, bbar, hfr⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hcx]
      exact (hLℓ ℓ).2.2 ρA hA ρd hd ⟨b, bbar, hfr⟩ c hc
    exact fun y hy => this hy

  let φ : ↥Y →ₗ[k] (↥Lp × (∀ ℓ : ↥(S'.erase (pPrime p)), ↥(Lℓ ℓ))) :=
    LinearMap.prod
      (LinearMap.codRestrict Lp ((res M (loc (pPrime p))).comp Y.subtype) fun y => hYp y y.2)
      (LinearMap.pi fun ℓ =>
        LinearMap.codRestrict (Lℓ ℓ) ((res M (loc (ℓ : Nat.Primes))).comp Y.subtype)
          fun y => hYℓ ℓ y y.2)

  set X : Submodule k (H1 M) := Y ⊓ ⨅ q ∈ S', LinearMap.ker (res M (loc q)) with hXdef
  have hkerφ : (LinearMap.ker φ).map Y.subtype ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hy
    have hy1 : res M (loc (pPrime p)) (y : H1 M) = 0 := by
      have := congrArg Prod.fst hy
      exact congrArg Subtype.val this
    have hy2 : ∀ ℓ : ↥(S'.erase (pPrime p)), res M (loc (ℓ : Nat.Primes)) (y : H1 M) = 0 := by
      intro ℓ
      have := congrFun (congrArg Prod.snd hy) ℓ
      exact congrArg Subtype.val this
    refine Submodule.mem_inf.2 ⟨y.2, ?_⟩
    rw [Submodule.mem_iInf]
    intro q
    rw [Submodule.mem_iInf]
    intro hq
    rw [LinearMap.mem_ker]
    by_cases hqp : q = pPrime p
    · subst hqp; exact hy1
    · exact hy2 ⟨q, Finset.mem_erase.2 ⟨hqp, hq⟩⟩

  obtain ⟨Ψ, hΨbij, hΨπ, hΨfin⟩ :=
    groupCohomology.exists_bijective_H1_map_of_restrictScalars (k := ZMod p) (K := k)
      ρbar.adZeroRep ρ₀ hρ₀
  have hMur : ∀ q : Nat.Primes, q ∉ S' ∪ Q → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (M₀).ρ g = 1 :=
    fun q hq => hMur₀ hρ₀ (S' ∪ Q) (fun q' hq' => hur q' fun h => hq' (Finset.mem_union_left _ h)) q hq
  have hadm₀ : admSub (M₀) (S' ∪ Q) = continuousH1S (S' ∪ Q) (M₀) :=
    groupCohomology.eq_continuousH1S_of_forall_mem_iff (S' ∪ Q) (M₀) hMur (admSub (M₀) (S' ∪ Q))
      (fun x => mem_admSub_iff (M₀) (S' ∪ Q) x)
  have hcomap : X.comap Ψ ≤ Sel := by
    intro w hw
    rw [Submodule.mem_comap] at hw
    obtain ⟨hwY, hwK⟩ := Submodule.mem_inf.1 hw

    obtain ⟨c, hclc, hcur, hcw⟩ := hYadm hwY

    have hcmem : (⇑c : Γ → LinearMap.ker (LinearMap.trace k ρbar.V)) ∈ cocycles₁ (M₀) := by
      rw [mem_cocycles₁_iff]
      intro g h
      have := (mem_cocycles₁_iff (A := M) c).1 c.2 g h
      change c (g * h) = ρ₀ g (c h) + c g
      rw [hρ₀]
      exact this
    set c₀ : cocycles₁ (M₀) := ⟨⇑c, hcmem⟩ with hc₀def
    have hc₀ : (c₀ : Γ → LinearMap.ker (LinearMap.trace k ρbar.V)) = c := rfl
    have hΨc₀ : Ψ (H1π (M₀) c₀) = H1π M c := hΨπ c₀ c hc₀
    have hw : w = H1π (M₀) c₀ := hΨbij.1 (by rw [hΨc₀, hcw])
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    ·
      rw [← hadm₀, hw]
      refine ⟨c₀, hclc, fun q hq A hA => ?_, rfl⟩
      obtain ⟨m, hm⟩ := hcur q hq A hA
      refine ⟨m, fun g hg => ?_⟩
      change c g = ρ₀ g m - m
      rw [hρ₀]
      exact hm g hg
    ·
      rw [Submodule.mem_iInf]
      intro q
      rw [Submodule.mem_iInf]
      intro hq
      rw [LinearMap.mem_ker, hw]
      have hq' : res M (loc q) (Ψ w) = 0 := by
        rw [Submodule.mem_iInf] at hwK
        have := hwK q
        rw [Submodule.mem_iInf] at this
        exact this hq
      rw [← hcw] at hq'
      obtain ⟨m, hm⟩ := (res_H1π_eq_zero_iff M (loc q) c).1 hq'
      change res (M₀) (loc q) (H1π (M₀) c₀) = 0
      rw [res_H1π_eq_zero_iff]
      refine ⟨m, fun h => ?_⟩
      change c (loc q h) = ρ₀ (loc q h) m - m
      rw [hρ₀]
      exact hm h
  haveI hXcfd : FiniteDimensional (ZMod p) ↥(X.comap Ψ) := Submodule.finiteDimensional_of_le hcomap

  haveI hXfd : FiniteDimensional k X := by
    haveI : Finite ↥(X.comap Ψ) := Module.finite_of_finite (ZMod p)
    have hsurj : Function.Surjective (fun w : ↥(X.comap Ψ) => (⟨Ψ w, w.2⟩ : ↥X)) := by
      rintro ⟨x, hx⟩
      obtain ⟨w, rfl⟩ := hΨbij.2 x
      exact ⟨⟨w, hx⟩, rfl⟩
    haveI : Finite ↥X := Finite.of_surjective _ hsurj
    exact Module.Finite.of_finite
  have hXdim : f * Module.finrank k X ≤ Module.finrank (ZMod p) Sel := by
    rw [hfdef, ← hΨfin X]
    exact Submodule.finrank_mono hcomap

  haveI hkerfd : FiniteDimensional k ↥(LinearMap.ker φ) := by
    haveI : FiniteDimensional k ↥((LinearMap.ker φ).map Y.subtype) :=
      Submodule.finiteDimensional_of_le hkerφ
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective Y.subtype (Submodule.injective_subtype Y) (LinearMap.ker φ)).symm
  haveI hYfd : FiniteDimensional k ↥Y := by
    have hmap : ((⊤ : Submodule k ↥Y).map φ).FG := IsNoetherian.noetherian _
    have hker : ((⊤ : Submodule k ↥Y) ⊓ LinearMap.ker φ).FG := by
      rw [top_inf_eq]
      exact (Submodule.fg_top _).1 Module.Finite.fg_top
    exact ⟨Submodule.fg_of_fg_map_of_fg_inf_ker φ hmap hker⟩
  have hRN : Module.finrank k ↥(LinearMap.range φ) + Module.finrank k ↥(LinearMap.ker φ) =
      Module.finrank k ↥Y := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank k ↥(LinearMap.range φ) ≤
      Module.finrank k Lp + ∑ ℓ : ↥(S'.erase (pPrime p)), Module.finrank k ↥(Lℓ ℓ) := by
    calc Module.finrank k ↥(LinearMap.range φ)
        ≤ Module.finrank k (↥Lp × (∀ ℓ : ↥(S'.erase (pPrime p)), ↥(Lℓ ℓ))) := Submodule.finrank_le _
      _ = Module.finrank k Lp + ∑ ℓ : ↥(S'.erase (pPrime p)), Module.finrank k ↥(Lℓ ℓ) := by
        rw [Module.finrank_prod, Module.finrank_pi_fintype]
  have hkerdim : Module.finrank k ↥(LinearMap.ker φ) ≤ Module.finrank k X := by
    rw [← Submodule.finrank_map_subtype_eq Y (LinearMap.ker φ)]
    exact Submodule.finrank_mono hkerφ

  have hLp' : Module.finrank k Lp ≤ Module.finrank k (Rep.res (loc (pPrime p)) M).ρ.invariants + 1 :=
    hLp.2.1
  have hLℓ' : ∑ ℓ : ↥(S'.erase (pPrime p)), Module.finrank k ↥(Lℓ ℓ) ≤
      ∑ ℓ ∈ S'.erase (pPrime p), Module.finrank k (Rep.res (loc ℓ) M).ρ.invariants := by
    rw [← Finset.sum_coe_sort (S'.erase (pPrime p))]
    exact Finset.sum_le_sum fun ℓ _ => (hLℓ ℓ).2.1
  have hsplit : ∑ q ∈ S', Module.finrank k (Rep.res (loc q) M).ρ.invariants =
      Module.finrank k (Rep.res (loc (pPrime p)) M).ρ.invariants +
        ∑ ℓ ∈ S'.erase (pPrime p), Module.finrank k (Rep.res (loc ℓ) M).ρ.invariants :=
    (Finset.add_sum_erase S' (fun q => Module.finrank k (Rep.res (loc q) M).ρ.invariants) hpS).symm

  have hbot : continuousH1S (S' ∪ Q) ((Rep.of ρ₀).dualTwist (cycloChar p)) ⊓
      ⨅ q ∈ Q, LinearMap.ker (groupCohomology.map (primeLocalToGlobal q)
        (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine hkill x hx1 fun q hq => ?_
    rw [Submodule.mem_iInf] at hx2
    have := hx2 q
    rw [Submodule.mem_iInf] at this
    exact this hq
  have hGW := ResidualGaloisRep.finrank_strictSelmer_adZero_le_card_taylorWilesPrimes_add_finrank_dualSelmer
    p hp2 ρbar habs hdet hTW ρ₀ hρ₀ S' Q hpS hSQ hur hQ
  rw [hbot, finrank_bot, add_zero, hsplit] at hGW
  change Module.finrank (ZMod p) ↥Sel + f + f * _ ≤ f * Q.card at hGW

  have key : f * Module.finrank k ↥Y ≤ f * Q.card := by
    have h1 : f * Module.finrank k ↥(LinearMap.range φ) ≤
        f * (Module.finrank k (Rep.res (loc (pPrime p)) M).ρ.invariants + 1 +
          ∑ ℓ ∈ S'.erase (pPrime p), Module.finrank k (Rep.res (loc ℓ) M).ρ.invariants) :=
      Nat.mul_le_mul_left f (hrange.trans (add_le_add hLp' hLℓ'))
    have h2 : f * Module.finrank k ↥(LinearMap.ker φ) ≤ Module.finrank (ZMod p) ↥Sel :=
      (Nat.mul_le_mul_left f hkerdim).trans hXdim
    calc f * Module.finrank k ↥Y
        = f * Module.finrank k ↥(LinearMap.range φ) + f * Module.finrank k ↥(LinearMap.ker φ) := by
          rw [← hRN, mul_add]
      _ ≤ f * (Module.finrank k (Rep.res (loc (pPrime p)) M).ρ.invariants + 1 +
            ∑ ℓ ∈ S'.erase (pPrime p), Module.finrank k (Rep.res (loc ℓ) M).ρ.invariants) +
          Module.finrank (ZMod p) ↥Sel := add_le_add h1 h2
      _ = Module.finrank (ZMod p) ↥Sel + f +
          f * (Module.finrank k (Rep.res (loc (pPrime p)) M).ρ.invariants +
            ∑ ℓ ∈ S'.erase (pPrime p), Module.finrank k (Rep.res (loc ℓ) M).ρ.invariants) := by ring
      _ ≤ f * Q.card := hGW
  exact Nat.le_of_mul_le_mul_left key hfpos

end Core

section ResRep

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k]
variable (ρbar : ResidualGaloisRep k)
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  [IsScalarTower (ZMod p) k (LinearMap.ker (LinearMap.trace k ρbar.V))]

def resRep : Representation (ZMod p) Γ (LinearMap.ker (LinearMap.trace k ρbar.V)) where
  toFun g := (ρbar.adZeroRep g).restrictScalars (ZMod p)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

lemma resRep_apply (g : Γ) (v : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    resRep (p := p) ρbar g v = ρbar.adZeroRep g v := rfl

end ResRep

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [Finite (ResidueField 𝒪)]

local notation "𝕜" => ResidueField 𝒪

set_option maxHeartbeats 4000000 in

theorem road (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP 𝕜 p]
    (ρbar : ResidualGaloisRep 𝕜)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : 𝕜, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra 𝕜 K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (S Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (𝒟 : Finset ℕ → GaloisRepAdic (DualNumber 𝕜) → Prop)
    (h𝒟ur : ∀ T ρA, 𝒟 T ρA → ∀ q : ℕ, q.Prime → q ∉ T → ρA.IsUnramifiedAt q)
    (condP : GaloisRepAdic (DualNumber 𝕜) → Prop)
    (h𝒟p : ∀ T ρA, 𝒟 T ρA → condP ρA)
    (hBp : ∃ L : Submodule 𝕜 (H1 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)),
      FiniteDimensional 𝕜 L ∧
      Module.finrank 𝕜 L ≤
        Module.finrank 𝕜 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants + 1 ∧
      ∀ (ρA : GaloisRepAdic (DualNumber 𝕜)), condP ρA →
        ∀ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End 𝕜 ρbar.V))ˣ,
          IsDualLift ρbar.ρ.toHomUnits ρd →
          (∃ (b : Module.Basis (Fin 2) (DualNumber 𝕜) ρA.V) (bbar : Module.Basis (Fin 2) 𝕜 ρbar.V),
            ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
              Matrix.dualNumberEquiv.symm
                ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End 𝕜 ρbar.V)).fst),
                  LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End 𝕜 ρbar.V)).snd)⟩) →
          ∀ c : cocycles₁ ρbar.adZero,
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace 𝕜 ρbar.V))) σ : Module.End 𝕜 ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) →
            (groupCohomology.map (primeLocalToGlobal (pPrime p))
              (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈ L) :
    ∃ r : ℕ, ∀ n : ℕ, ∃ qv : Fin r → ℕ, Function.Injective qv ∧
      (∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ^ (n + 1) ∣ qv i - 1) ∧
      (∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ (qv i) →
          ∃ α β : 𝕜, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      Module.finrank 𝕜 (Submodule.span 𝕜
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber 𝕜),
            (𝒟 (Smin ∪ Finset.univ.image qv) ρA ∧
                ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q) ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End 𝕜 ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace 𝕜 ρbar.V))) σ :
                  Module.End 𝕜 ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber 𝕜) ρA.V)
              (bbar : Module.Basis (Fin 2) 𝕜 ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End 𝕜 ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End 𝕜 ρbar.V)).snd)⟩}) ≤ r := by
  classical

  letI : Algebra (ZMod p) 𝕜 := ZMod.algebra 𝕜 p
  letI : Module (ZMod p) (LinearMap.ker (LinearMap.trace 𝕜 ρbar.V)) :=
    Module.compHom _ (algebraMap (ZMod p) 𝕜)
  haveI : IsScalarTower (ZMod p) 𝕜 (LinearMap.ker (LinearMap.trace 𝕜 ρbar.V)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : Representation (ZMod p) Γ (LinearMap.ker (LinearMap.trace 𝕜 ρbar.V)),
      ρ₀ = resRep (p := p) ρbar := ⟨_, rfl⟩
  have hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v := fun g v => by rw [hρ₀def]; rfl

  obtain ⟨S', hS'def⟩ : ∃ S' : Finset Nat.Primes, S' = Smin.subtype Nat.Prime := ⟨_, rfl⟩
  have hmemS' : ∀ q : Nat.Primes, q ∈ S' ↔ (q : ℕ) ∈ Smin := fun q => by
    rw [hS'def]; exact Finset.mem_subtype
  have hpS : pPrime p ∈ S' := (hmemS' _).2 hpSmin
  have hur : ∀ q : Nat.Primes, q ∉ S' → ρbar.IsUnramifiedAt q := by
    intro q hq
    have hq' : (q : ℕ) ∉ Smin := fun h => hq ((hmemS' q).2 h)
    have hne : (q : ℕ) ≠ p := fun h => hq' (h ▸ hpSmin)
    by_contra hram
    exact hq' ((hmin q q.2 hne).2 hram)

  obtain ⟨Lp, hLpfd, hLpdim, hLpmem⟩ := hBp
  have hℓ : ∀ ℓ : ↥(S'.erase (pPrime p)), ((ℓ : Nat.Primes) : ℕ) ≠ p ∧ ¬ ρbar.IsUnramifiedAt ℓ := by
    rintro ⟨ℓ, hℓ⟩
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hℓ
    have hne' : ((ℓ : Nat.Primes) : ℕ) ≠ p := fun h => hne (Subtype.ext h)
    exact ⟨hne', (hmin ℓ ℓ.2 hne').1 ((hmemS' ℓ).1 hmem)⟩
  choose Lℓ hLℓ using fun ℓ : ↥(S'.erase (pPrime p)) =>
    GaloisRepAdic.exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt p hp2 ρbar
      (ℓ : Nat.Primes) (hℓ ℓ).1 (hℓ ℓ).2

  refine ⟨Module.finrank (ZMod p) (continuousH1S S' ((Rep.of ρ₀).dualTwist (cycloChar p))), fun n => ?_⟩
  obtain ⟨Q, hQcard, hQprop, hQkill⟩ :=
    ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist p hp2 ρbar habs
      hsplit hTW ρ₀ hρ₀ S' hpS hur (n + 1) S
  obtain ⟨e⟩ : Nonempty (↥Q ≃ Fin (Module.finrank (ZMod p)
      (continuousH1S S' ((Rep.of ρ₀).dualTwist (cycloChar p))))) := ⟨Finset.equivFinOfCardEq hQcard⟩
  obtain ⟨qv, hqvi⟩ : ∃ qv : Fin (Module.finrank (ZMod p)
      (continuousH1S S' ((Rep.of ρ₀).dualTwist (cycloChar p)))) → ℕ,
      ∀ i, qv i = (((e.symm i : ↥Q) : Nat.Primes) : ℕ) := ⟨_, fun _ => rfl⟩
  have hqv : ∀ i, ((e.symm i : ↥Q) : Nat.Primes) ∈ Q := fun i => (e.symm i).2
  refine ⟨qv, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hqvi, hqvi] at hij
    have : (e.symm i : ↥Q) = e.symm j := Subtype.ext (Subtype.ext hij)
    exact e.symm.injective this
  · intro i
    obtain ⟨hT, hmod, -, -⟩ := hQprop _ (hqv i)
    rw [hqvi]
    refine ⟨(e.symm i : ↥Q).1.2, hT, ?_⟩
    exact (Nat.modEq_iff_dvd' (e.symm i : ↥Q).1.2.one_lt.le).1 hmod.symm
  · intro i P hP φ hφ
    rw [hqvi] at hP hφ
    exact (hQprop _ (hqv i)).2.2.2 P hP φ hφ

  have hSQ : Disjoint S' Q := by
    rw [Finset.disjoint_left]
    intro q hqS hqQ
    exact (hQprop q hqQ).1 (hSmin ((hmemS' q).1 hqS))
  have hQ : ∀ q ∈ Q, (q : ℕ) ≡ 1 [MOD p] ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : 𝕜, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by
    intro q hq
    obtain ⟨-, hmod, -, hfrob⟩ := hQprop q hq
    exact ⟨hmod.of_dvd (dvd_pow_self p (Nat.succ_ne_zero n)), hfrob⟩
  have hnotin : ∀ q : Nat.Primes, q ∉ S' ∪ Q → (q : ℕ) ∉ Smin ∪ Finset.univ.image qv := by
    intro q hq h
    rcases Finset.mem_union.1 h with h | h
    · exact hq (Finset.mem_union_left _ ((hmemS' q).2 h))
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      have : q = ((e.symm i : ↥Q) : Nat.Primes) := Subtype.ext (by rw [← hi, hqvi])
      exact hq (Finset.mem_union_right _ (this ▸ hqv i))
  let 𝒞 : GaloisRepAdic (DualNumber 𝕜) → Prop := fun ρA =>
    𝒟 (Smin ∪ Finset.univ.image qv) ρA ∧ ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q
  have h𝒞ur : ∀ ρA, 𝒞 ρA → ∀ q : Nat.Primes, q ∉ S' ∪ Q → ρA.IsUnramifiedAt q :=
    fun ρA hA q hq => h𝒟ur _ ρA hA.1 q q.2 (hnotin q hq)
  have hLp : LocalBound ρbar 𝒞 (pPrime p)
      (Module.finrank 𝕜 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants + 1) Lp :=
    ⟨hLpfd, hLpdim, fun ρA hA ρd hd hfr c hc => hLpmem ρA (h𝒟p _ ρA hA.1) ρd hd hfr c hc⟩
  have hLℓ' : ∀ ℓ : ↥(S'.erase (pPrime p)), LocalBound ρbar 𝒞 ℓ
      (Module.finrank 𝕜 (Rep.res (primeLocalToGlobal (ℓ : Nat.Primes)) ρbar.adZero).ρ.invariants) (Lℓ ℓ) := by
    intro ℓ
    refine ⟨(hLℓ ℓ).1, (hLℓ ℓ).2.1, fun ρA hA ρd hd hfr c hc => (hLℓ ℓ).2.2 ρA ?_ ρd hd hfr c hc⟩
    have hmem : ((ℓ : Nat.Primes) : ℕ) ∈ Smin :=
      (hmemS' _).1 (Finset.mem_erase.1 ℓ.2).2
    exact hA.2 _ hmem (ℓ : Nat.Primes).2 (hℓ ℓ).1
  have hcount := finrank_span_le p ρbar ρ₀ hρ₀ hp2 habs hdet hTW S' Q hpS hSQ hur hQ hQkill 𝒞 h𝒞ur
    Lp hLp Lℓ hLℓ'
  calc _ ≤ Q.card := hcount
    _ = _ := hQcard

end Main

end P2mK4NS

end

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : ResidueField 𝒪, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra (ResidueField 𝒪) K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (S Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S) (hS : ∀ q ∈ S, q.Prime)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q)) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    (∃ r : ℕ, ∀ n : ℕ, ∃ qv : Fin r → ℕ, Function.Injective qv ∧
      (∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ^ (n + 1) ∣ qv i - 1) ∧
      (∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ (qv i) →
          ∃ α β : ResidueField 𝒪, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            (GaloisRep.strictOrdinaryCondition 𝒪 p (Smin ∪ Finset.univ.image qv) ρA ∧
                ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q) ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) ≤ r) ∧
    (∃ r : ℕ, ∀ n : ℕ, ∃ qv : Fin r → ℕ, Function.Injective qv ∧
      (∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ^ (n + 1) ∣ qv i - 1) ∧
      (∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ (qv i) →
          ∃ α β : ResidueField 𝒪, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            (GaloisRep.flatCondition 𝒪 p (Smin ∪ Finset.univ.image qv) ρA ∧
                ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q) ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) ≤ r) :=
  by
  letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
    ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
      (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
  haveI hchar : CharP (ResidueField 𝒪) p := by
    refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
    have h : IsLocalRing.residue 𝒪 (p : 𝒪) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hp𝒪
    rwa [map_natCast] at h
  exact ⟨P2mK4NS.road p hp2 ρbar habs hdet hsplit hTW S Smin hpSmin hSmin hmin
      (fun T ρA => GaloisRep.strictOrdinaryCondition 𝒪 p T ρA) (fun T ρA h => h.2.2)
      (fun ρA => ρA.IsStrictOrdinaryAt p) (fun T ρA h => h.2.1)
      (GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt p hp2 ρbar),
    P2mK4NS.road p hp2 ρbar habs hdet hsplit hTW S Smin hpSmin hSmin hmin
      (fun T ρA => GaloisRep.flatCondition 𝒪 p T ρA) (fun T ρA h => h.2.2)
      (fun ρA => ρA.IsFlatAt p) (fun T ρA h => h.2.1)
      (GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt p hp2 ρbar)⟩

end S_ResidualGaloisRep_exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary
end P2MW
export P2MW.S_ResidualGaloisRep_exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary (solution)

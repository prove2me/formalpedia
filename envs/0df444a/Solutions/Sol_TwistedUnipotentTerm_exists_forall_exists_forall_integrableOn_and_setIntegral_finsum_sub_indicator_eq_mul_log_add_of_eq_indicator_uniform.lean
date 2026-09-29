-- Prove2me | solution 1 for TwistedUnipotentTerm.exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/820b046f-058f-5c53-85bf-7bd9e1b10c27

import Theorems.Thm_TwistedUnipotentTerm_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
import Theorems.Thm_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul"
p2m_attr_erase "simp" "FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero"
p2m_attr_erase "simp" "NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

noncomputable section

namespace TwistedUnipotentTerm
p2m_export "TwistedUnipotentTerm" "exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator"
namespace UniformCoefficient
p2m_open "TwistedUnipotentTerm"

section Local

open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem preimage_mul_left_eq_smul (u : (v.adicCompletion K)ˣ) (s : Set (v.adicCompletion K)) :
    (fun x => (u : v.adicCompletion K) * x) ⁻¹' s = u⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

theorem coe_modulus_uniformizerUnit :
    ((modulus (NumberField.AdelicLevel.uniformizerUnit K v : v.adicCompletion K) : ℝ)) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [modulus_adicCompletion_eq_nnnorm K v, coe_nnnorm, NumberField.FinitePlace.norm_def,
    NumberField.AdelicLevel.valued_uniformizerUnit,
    show (WithZero.exp (-1 : ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero]
  simp only [WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv, NNReal.coe_natCast]

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

theorem measurable_modulus : Measurable (modulus : v.adicCompletion K → ℝ≥0) := by
  have h : (modulus : v.adicCompletion K → ℝ≥0) = fun x => ‖x‖₊ :=
    funext (modulus_adicCompletion_eq_nnnorm K v)
  rw [h]
  exact measurable_nnnorm

theorem map_mul_left_eq_smul (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (u : (v.adicCompletion K)ˣ) :
    Measure.map (fun x => (u : v.adicCompletion K) * x) μ =
      ((modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, preimage_mul_left_eq_smul, Measure.smul_apply,
    smul_eq_mul, ← distribHaarChar_mul μ u⁻¹ s, map_inv, modulus_coe_units,
    ENNReal.coe_inv distribHaarChar_pos.ne']

theorem localZeta_comp_mul_left (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (u : (v.adicCompletion K)ˣ) (f : v.adicCompletion K → ℂ) (s : ℂ) :
    localZeta μ (fun t => f ((u : v.adicCompletion K) * t)) 1 s =
      ((modulus (u : v.adicCompletion K) : ℝ) : ℂ) ^ (-s) * localZeta μ f 1 s := by
  set c : ℝ≥0 := modulus (u : v.adicCompletion K) with hc
  have hc0 : c ≠ 0 := modulus_ne_zero u.ne_zero
  have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (modulus_pos u.ne_zero)
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'

  set d : v.adicCompletion K → ℝ≥0∞ := fun x => ((modulus x : ℝ≥0∞))⁻¹ with hd
  have hdm : Measurable d := (measurable_coe_nnreal_ennreal.comp (measurable_modulus v)).inv
  set ρ : Measure (v.adicCompletion K) := μ.restrict {0}ᶜ with hρ
  have hd_lt : ∀ᵐ x ∂ρ, d x < ∞ := by
    refine (ae_restrict_mem (measurableSet_singleton (0 : v.adicCompletion K)).compl).mono
      fun x hx => ?_
    have hx0 : x ≠ 0 := hx
    simp only [hd, ENNReal.inv_lt_top, ENNReal.coe_pos]
    exact modulus_pos hx0

  have hmapρ : Measure.map (fun x => (u : v.adicCompletion K) * x) ρ = ((c : ℝ≥0∞)⁻¹) • ρ := by
    have hpre : (fun x => (u : v.adicCompletion K) * x) ⁻¹' ({0}ᶜ : Set (v.adicCompletion K)) = {0}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero, u.ne_zero,
        false_or]
    calc Measure.map (fun x => (u : v.adicCompletion K) * x) ρ
        = Measure.map (fun x => (u : v.adicCompletion K) * x)
            (μ.restrict ((fun x => (u : v.adicCompletion K) * x) ⁻¹' {0}ᶜ)) := by rw [hpre]
      _ = (Measure.map (fun x => (u : v.adicCompletion K) * x) μ).restrict {0}ᶜ :=
          (Measure.restrict_map (measurable_const_mul _) (measurableSet_singleton 0).compl).symm
      _ = ((c : ℝ≥0∞)⁻¹) • ρ := by rw [map_mul_left_eq_smul, Measure.restrict_smul]

  have hZ : ∀ G : v.adicCompletion K → ℂ, localZeta μ G 1 s =
      ∫ x, (d x).toReal • (G x * charExt (1 : (v.adicCompletion K)ˣ →* ℂˣ) x *
        ((modulus x : ℝ) : ℂ) ^ s) ∂ρ := fun G => by
    show ∫ x, _ ∂((μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹) = _
    exact integral_withDensity_eq_integral_toReal_smul hdm hd_lt _
  set Φ : v.adicCompletion K → ℂ := fun x => (d x).toReal •
    (f x * charExt (1 : (v.adicCompletion K)ˣ →* ℂˣ) x * ((modulus x : ℝ) : ℂ) ^ s) with hΦ

  have hpt : ∀ x : v.adicCompletion K,
      (d x).toReal • (f ((u : v.adicCompletion K) * x) * charExt (1 : (v.adicCompletion K)ˣ →* ℂˣ) x *
          ((modulus x : ℝ) : ℂ) ^ s)
        = ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-s) * Φ ((u : v.adicCompletion K) * x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [hΦ, hd]
    · have hux : (u : v.adicCompletion K) * x ≠ 0 := mul_ne_zero u.ne_zero hx
      have hmx : 0 < modulus x := modulus_pos hx
      have hmxR : (0 : ℝ) < (modulus x : ℝ) := NNReal.coe_pos.mpr hmx
      have hmod : modulus ((u : v.adicCompletion K) * x) = c * modulus x := modulus_mul _ _
      have hdx : (d x).toReal = ((modulus x : ℝ))⁻¹ := by
        simp only [hd, ENNReal.toReal_inv, ENNReal.coe_toReal]
      have hdux : (d ((u : v.adicCompletion K) * x)).toReal = ((c : ℝ))⁻¹ * ((modulus x : ℝ))⁻¹ := by
        simp only [hd, hmod, ENNReal.toReal_inv, ENNReal.coe_toReal, NNReal.coe_mul, mul_inv]
      have hcpow : (((c * modulus x : ℝ≥0) : ℝ) : ℂ) ^ s = ((c : ℝ) : ℂ) ^ s * ((modulus x : ℝ) : ℂ) ^ s := by
        rw [NNReal.coe_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hcpos.le hmxR.le]
      simp only [hΦ]
      rw [hdx, hdux, hmod, hcpow, charExt_one_of_ne_zero hx, charExt_one_of_ne_zero hux, Complex.real_smul,
        Complex.real_smul, Complex.cpow_neg, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_inv]
      have hcs : ((c : ℝ) : ℂ) ^ s ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
        exact Or.inl hcC
      field_simp

  have hmapΦ : ∫ x, Φ x ∂(Measure.map (fun x => (u : v.adicCompletion K) * x) ρ) =
      ∫ x, Φ ((u : v.adicCompletion K) * x) ∂ρ := by
    rw [← MeasurableEquiv.coe_mulLeft₀ u.ne_zero, integral_map_equiv]
    rfl
  rw [hZ, hZ f]
  calc ∫ x, (d x).toReal • (f ((u : v.adicCompletion K) * x) *
          charExt (1 : (v.adicCompletion K)ˣ →* ℂˣ) x * ((modulus x : ℝ) : ℂ) ^ s) ∂ρ
      = ∫ x, ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-s) * Φ ((u : v.adicCompletion K) * x) ∂ρ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-s) * ∫ x, Φ ((u : v.adicCompletion K) * x) ∂ρ :=
        integral_const_mul _ _
    _ = ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-s) * ∫ x, Φ x ∂(((c : ℝ≥0∞)⁻¹) • ρ) := by
        rw [← hmapρ, hmapΦ]
    _ = ((c : ℝ) : ℂ) ^ (-s) * ∫ x, Φ x ∂ρ := by
        rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul,
          Complex.ofReal_inv]
        field_simp

end Local

section Global

open NumberField.TateGlobal NumberField.AdelicFourier
open scoped NNReal ENNReal Pointwise

variable (F : Type) [Field F] [NumberField F]

abbrev principalIdeles : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

theorem countable_principalIdeles : Countable (principalIdeles F) := by
  haveI : Countable F := Countable.of_equiv _ (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable Fˣ := Units.val_injective.countable
  exact (Set.countable_range _).to_subtype

theorem ideleNorm_unitsMap (η : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) η) = 1 := by
  have hdet : Matrix.det (Matrix.diagonal ![(η : F), 1]) ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]
  have hγ : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) = η :=
    Units.ext (by
      show Matrix.det (Matrix.diagonal ![(η : F), 1]) = (η : F)
      simp [Matrix.det_diagonal, Fin.prod_univ_two])
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)
  rw [show AutomorphicForm.globalPoints (𝓞 F) F =
      Matrix.GeneralLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F)) from rfl,
    Matrix.GeneralLinearGroup.map_det, hγ] at h
  exact h

theorem ideleNorm_coe_principalIdeles (γ : principalIdeles F) :
    ideleNorm F (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  obtain ⟨η, hη⟩ := γ.2
  rw [← hη]
  exact ideleNorm_unitsMap F η

theorem ideleNorm_inv (y : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F y⁻¹ = (ideleNorm F y)⁻¹ := by
  simp [ideleNorm, map_inv]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)]

def rk (μ : Measure (AdeleRing (𝓞 F) F)) (Ψ : AdeleRing (𝓞 F) F → ℂ) (X : ℝ) (y : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((ideleNorm F y : ℝ) : ℂ)⁻¹ *
    ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
        AdeleRing (𝓞 F) F))) -
      (if X < ideleNorm F y then ((ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0))

theorem rk_smul (μ : Measure (AdeleRing (𝓞 F) F)) (Ψ : AdeleRing (𝓞 F) F → ℂ) (X : ℝ)
    (γ : principalIdeles F) (y : (AdeleRing (𝓞 F) F)ˣ) : rk F μ Ψ X (γ • y) = rk F μ Ψ X y := by
  obtain ⟨η₀, hη₀⟩ := γ.2
  have hn : ideleNorm F (γ • y) = ideleNorm F y := by
    rw [Subgroup.smul_def, smul_eq_mul, ideleNorm_mul, ideleNorm_coe_principalIdeles, one_mul]
  have key : ∀ η : Fˣ, algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
      (((γ • y)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
        algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.mulRight η₀⁻¹ η : Fˣ) : F) *
          ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
    intro η
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, Units.val_mul, ← hη₀, ← map_inv, Units.coe_map,
      Equiv.coe_mulRight, Units.val_mul, map_mul]
    show algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
        (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) ↑η₀⁻¹) = _
    ring
  have hsum : (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
      (((γ • y)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) =
        ∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
          ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    simp_rw [key]
    exact finsum_comp_equiv (Equiv.mulRight η₀⁻¹)
      (f := fun η : Fˣ => Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
        ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)))
  unfold rk
  rw [hn, hsum]

theorem rk_comp_mul (μ : Measure (AdeleRing (𝓞 F) F)) (Ψ : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ)
    (hM : ∫ u, Ψ (↑a * u) ∂μ = ((ideleNorm F a : ℝ) : ℂ)⁻¹ * ∫ u, Ψ u ∂μ) (X : ℝ)
    (y : (AdeleRing (𝓞 F) F)ˣ) :
    rk F μ (fun x => Ψ (↑a * x)) X y =
      ((ideleNorm F a : ℝ) : ℂ)⁻¹ * rk F μ Ψ (X / ideleNorm F a) (y * a⁻¹) := by
  have ha : 0 < ideleNorm F a := ideleNorm_pos a
  have hy : 0 < ideleNorm F y := ideleNorm_pos y
  have haC : ((ideleNorm F a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hyC : ((ideleNorm F y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hn : ideleNorm F (y * a⁻¹) = ideleNorm F y / ideleNorm F a := by
    rw [ideleNorm_mul, ideleNorm_inv, div_eq_mul_inv]
  have hprod : ∀ η : Fˣ, (↑a : AdeleRing (𝓞 F) F) * (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) =
        algebraMap F (AdeleRing (𝓞 F) F) (η : F) * (((y * a⁻¹)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
    intro η
    rw [mul_inv_rev, inv_inv, Units.val_mul]
    ring
  have hcond : (X / ideleNorm F a < ideleNorm F y / ideleNorm F a) ↔ (X < ideleNorm F y) :=
    div_lt_div_iff_of_pos_right ha
  simp only [rk, hprod, hM, hn]
  by_cases hX : X < ideleNorm F y
  · rw [if_pos hX, if_pos (hcond.mpr hX), Complex.ofReal_div]
    field_simp
  · rw [if_neg hX, if_neg (fun h => hX (hcond.mp h)), Complex.ofReal_div]
    field_simp

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] in

theorem setIntegral_comp_mul_right [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain (principalIdeles F) Ω ν) (f : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hf : ∀ (γ : principalIdeles F) (y : (AdeleRing (𝓞 F) F)ˣ), f (γ • y) = f y)
    (a : (AdeleRing (𝓞 F) F)ˣ) :
    ∫ y in Ω, f (y * a) ∂ν = ∫ y in Ω, f y ∂ν := by
  haveI := countable_principalIdeles F
  haveI : MeasurableConstSMul (principalIdeles F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun γ => (continuous_const_mul (γ : (AdeleRing (𝓞 F) F)ˣ)).measurable⟩
  haveI : SMulInvariantMeasure (principalIdeles F) (AdeleRing (𝓞 F) F)ˣ ν :=
    ⟨fun γ s hs => measure_preimage_mul ν (γ : (AdeleRing (𝓞 F) F)ˣ) s⟩
  haveI : MeasurableConstSMul (AdeleRing (𝓞 F) F)ˣ (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun g => (continuous_const_mul g).measurable⟩
  haveI : SMulInvariantMeasure (AdeleRing (𝓞 F) F)ˣ (AdeleRing (𝓞 F) F)ˣ ν :=
    ⟨fun g s hs => measure_preimage_mul ν g s⟩
  haveI : SMulCommClass (AdeleRing (𝓞 F) F)ˣ (principalIdeles F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun g γ x => mul_left_comm g (γ : (AdeleRing (𝓞 F) F)ˣ) x⟩
  have he : MeasurePreserving (fun y : (AdeleRing (𝓞 F) F)ˣ => y * a) ν ν := measurePreserving_mul_right ν a
  have hemb : MeasurableEmbedding (fun y : (AdeleRing (𝓞 F) F)ˣ => y * a) :=
    (MeasurableEquiv.mulRight a).measurableEmbedding
  have hpre : (fun y : (AdeleRing (𝓞 F) F)ˣ => y * a) ⁻¹' (a • Ω) = Ω := by
    ext y
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_comm y a, inv_mul_cancel_left]
  have h1 := he.setIntegral_preimage_emb hemb f (a • Ω)
  rw [hpre] at h1
  rw [h1]
  exact (hΩ.smul_of_comm a).setIntegral_eq hΩ hf

theorem integral_comp_mul_left [BorelSpace (AdeleRing (𝓞 F) F)] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] (Ψ : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ∫ u, Ψ (↑a * u) ∂μ = ((ideleNorm F a : ℝ) : ℂ)⁻¹ * ∫ u, Ψ u ∂μ := by
  have h0 : ∀ f : AdeleRing (𝓞 F) F → ℂ,
      fourierIntegral (0 : AddChar (AdeleRing (𝓞 F) F) ℂ) μ f 0 = ∫ u, f u ∂μ := fun f => by
    simp only [fourierIntegral, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have h := NumberField.AdelicFourier.fourierIntegral_comp_mul_left F μ (0 : AddChar (AdeleRing (𝓞 F) F) ℂ) Ψ a 0
  rw [mul_zero, h0, h0] at h
  exact h

end Global

section Main

open NumberField.TateGlobal NumberField.AdelicFourier NumberField.AdelicLevel LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

def unitAt {F : Type} [Field F] [NumberField F] (b : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ :=
  ⟨(b : FiniteAdeleRing (𝓞 F) F) w, ((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w,
    by rw [← coe_mul_apply, Units.mul_inv, coe_one_apply],
    by rw [← coe_mul_apply, Units.inv_mul, coe_one_apply]⟩

theorem coe_unitAt {F : Type} [Field F] [NumberField F] (b : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) : (unitAt b w : w.adicCompletion F) = (b : FiniteAdeleRing (𝓞 F) F) w := rfl

theorem main
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₁ : ℂ, ∀ (g : InfiniteAdeleRing F → ℂ) (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
      (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ),
      (∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
        (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x) →
      (∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) → (∀ θ, HasCompactSupport (Ψ θ)) →
    ∃ c₀ : ℂ, ∀ θ : Θ, ∀ X : ℝ, 0 < X →
      IntegrableOn (rk F μ (Ψ θ) X) Ω ν ∧
      (∫ y in Ω, rk F μ (Ψ θ) X y ∂ν) =
        ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
            NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, Ψ θ u ∂μ) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
          c₁ * (∫ u, Ψ θ₀ u ∂μ) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1) := by
  classical

  set v0 : ℂ := ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) with hv0
  set P0 : ℂ := ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 with hP0def
  refine ⟨v0 / P0, fun g h₀ Ψ hΨ hΨs hΨc => ?_⟩
  by_cases hTe : T = ∅
  ·
    obtain ⟨c₀, c₁', H⟩ :=
      TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
        F μ hμ1 ν Ω hΩ S μf T hT g h₀ Θ h Ψ hΨ hΨs hΨc hloc θ₀ hθ₀
    refine ⟨c₀, fun θ X hX => ⟨(H θ X hX).1, ?_⟩⟩
    haveI : IsEmpty (T : Type) := Finset.isEmpty_coe_sort.mpr hTe
    have h2 := (H θ X hX).2
    simp only [Finset.sum_of_isEmpty, mul_zero, add_zero] at h2 ⊢
    exact h2

  obtain ⟨p, hpT⟩ := Finset.nonempty_iff_ne_empty.mpr hTe
  have hpS : p ∈ S := hT hpT

  set qn : ℕ := Ideal.absNorm p.asIdeal with hqn
  have hq1 : 1 < qn := NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hqR : (1 : ℝ) < (qn : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (qn : ℝ) := zero_lt_one.trans hqR
  have hqC : ((qn : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  have hlogq : ((Real.log (qn : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hqR).ne'

  set afin : (FiniteAdeleRing (𝓞 F) F)ˣ := localUnit (𝓞 F) F p (uniformizerUnit F p) with hafin
  set a : (AdeleRing (𝓞 F) F)ˣ := AutomorphicForm.uniformizerIdele F p with ha
  have ha_val : (a : AdeleRing (𝓞 F) F) = ((1 : InfiniteAdeleRing F), (afin : FiniteAdeleRing (𝓞 F) F)) := rfl
  have ha_fst : ∀ x : AdeleRing (𝓞 F) F, ((a : AdeleRing (𝓞 F) F) * x).1 = x.1 := fun x => by
    rw [ha_val]
    show (1 : InfiniteAdeleRing F) * x.1 = x.1
    exact one_mul _
  have ha_snd : ∀ (x : AdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)),
      (((a : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F) w =
        (afin : FiniteAdeleRing (𝓞 F) F) w * (x.2 : FiniteAdeleRing (𝓞 F) F) w := fun x w => by
    rw [ha_val]
    show ((afin : FiniteAdeleRing (𝓞 F) F) * x.2) w = _
    rfl
  have hafin_p : (afin : FiniteAdeleRing (𝓞 F) F) p = (uniformizerUnit F p : p.adicCompletion F) :=
    localUnit_apply_self (𝓞 F) F p _
  have hafin_ne : ∀ {w : HeightOneSpectrum (𝓞 F)}, w ≠ p → (afin : FiniteAdeleRing (𝓞 F) F) w = 1 :=
    fun hw => localUnit_apply_of_ne (𝓞 F) F p _ hw
  have ha_norm : ideleNorm F a = ((qn : ℝ))⁻¹ := ideleNorm_uniformizerIdele F p

  have hmod_p : ((modulus ((afin : FiniteAdeleRing (𝓞 F) F) p) : ℝ)) = ((qn : ℝ))⁻¹ := by
    rw [hafin_p]
    exact coe_modulus_uniformizerUnit p
  have hmod_ne : ∀ {w : HeightOneSpectrum (𝓞 F)}, w ≠ p → modulus ((afin : FiniteAdeleRing (𝓞 F) F) w) = 1 :=
    fun hw => by rw [hafin_ne hw, modulus_one]

  obtain ⟨hp, hhp⟩ : ∃ hp : Option Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ,
      hp = fun o v => Option.elim o (fun t => h θ₀ v ((afin : FiniteAdeleRing (𝓞 F) F) v * t)) (fun θ => h θ v) :=
    ⟨_, rfl⟩
  obtain ⟨Ψp, hΨp⟩ : ∃ Ψp : Option Θ → AdeleRing (𝓞 F) F → ℂ,
      Ψp = fun o => Option.elim o (fun x => Ψ θ₀ ((a : AdeleRing (𝓞 F) F) * x)) Ψ := ⟨_, rfl⟩
  have hp_some : ∀ θ, hp (some θ) = h θ := fun θ => by rw [hhp]; rfl
  have hp_none : ∀ v, hp none v = fun t => h θ₀ v ((afin : FiniteAdeleRing (𝓞 F) F) v * t) :=
    fun v => by rw [hhp]; rfl
  have hΨp_some : ∀ θ, Ψp (some θ) = Ψ θ := fun θ => by rw [hΨp]; rfl
  have hΨp_none : Ψp none = fun x => Ψ θ₀ ((a : AdeleRing (𝓞 F) F) * x) := by rw [hΨp]; rfl

  have hΨp_shape : ∀ o x, Ψp o x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then hp o v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x := by
    rintro (_ | θ) x
    · rw [hΨp_none]
      show Ψ θ₀ ((a : AdeleRing (𝓞 F) F) * x) = _
      rw [hΨ θ₀]
      have hmem : ((a : AdeleRing (𝓞 F) F) * x ∈ NumberField.TateGlobal.integralOutside S) ↔
          (x ∈ NumberField.TateGlobal.integralOutside S) := by
        simp only [NumberField.TateGlobal.integralOutside, Set.mem_setOf_eq]
        refine forall₂_congr fun w hw => ?_
        rw [ha_snd, hafin_ne (ne_of_mem_of_not_mem hpS hw).symm, one_mul]
      by_cases hx : x ∈ NumberField.TateGlobal.integralOutside S
      · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx, ha_fst]
        congr 1
        refine Finset.prod_congr rfl fun w hwS => ?_
        by_cases hwT : w ∈ T
        · rw [if_pos hwT, if_pos hwT, hp_none, ha_snd]
        · rw [if_neg hwT, if_neg hwT, ha_snd, hafin_ne (ne_of_mem_of_not_mem hpT hwT).symm, one_mul]
      · rw [Set.indicator_of_notMem (fun h' => hx (hmem.mp h')), Set.indicator_of_notMem hx]
    · rw [hΨp_some, hp_some]
      exact hΨ θ x
  have hΨp_sb : ∀ o, Ψp o ∈ NumberField.AdelicFourier.schwartzBruhat F := by
    rintro (_ | θ)
    · rw [hΨp_none]
      exact NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat F a (hΨs θ₀)
    · rw [hΨp_some]; exact hΨs θ
  have hΨp_cs : ∀ o, HasCompactSupport (Ψp o) := by
    rintro (_ | θ)
    · rw [hΨp_none]
      let φ : AdeleRing (𝓞 F) F ≃ₜ AdeleRing (𝓞 F) F :=
        { toEquiv := Units.mulLeft a
          continuous_toFun := continuous_const_mul _
          continuous_invFun := continuous_const_mul _ }
      exact (hΨc θ₀).comp_homeomorph φ
    · rw [hΨp_some]; exact hΨc θ

  have hzeta_none : ∀ (w : HeightOneSpectrum (𝓞 F)) (s : ℂ),
      localZeta (μf w) (hp none w) 1 s =
        ((modulus ((afin : FiniteAdeleRing (𝓞 F) F) w) : ℝ) : ℂ) ^ (-s) * localZeta (μf w) (h θ₀ w) 1 s :=
    fun w s => by
    rw [hp_none]
    exact localZeta_comp_mul_left w (μf w) (unitAt afin w) (h θ₀ w) s
  have hmodC_ne : ∀ w : HeightOneSpectrum (𝓞 F), ((modulus ((afin : FiniteAdeleRing (𝓞 F) F) w) : ℝ) : ℂ) ≠ 0 :=
    fun w => Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (modulus_pos (unitAt afin w).ne_zero)).ne'
  have hloc' : ∀ o, ∀ w ∈ T, DifferentiableOn ℂ (fun s : ℂ => localZeta (μf w) (hp o w) 1 s) {s : ℂ | 0 < s.re} := by
    rintro (_ | θ) w hw
    · have hfun : (fun s : ℂ => localZeta (μf w) (hp none w) 1 s) = fun s =>
          ((modulus ((afin : FiniteAdeleRing (𝓞 F) F) w) : ℝ) : ℂ) ^ (-s) * localZeta (μf w) (h θ₀ w) 1 s :=
        funext (hzeta_none w)
      rw [hfun]
      exact ((differentiableOn_id.neg).const_cpow (Or.inl (hmodC_ne w))).mul (hloc θ₀ w hw)
    · rw [hp_some]; exact hloc θ w hw
  have hθ₀' : ∏ i : T, localZeta (μf i) (hp (some θ₀) i) 1 1 ≠ 0 := by
    rw [hp_some]; exact hθ₀

  obtain ⟨c₀, c₁', H⟩ :=
    TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
      F μ hμ1 ν Ω hΩ S μf T hT g h₀ (Option Θ) hp Ψp hΨp_shape hΨp_sb hΨp_cs hloc' (some θ₀) hθ₀'
  have H' : ∀ (o : Option Θ) (X : ℝ), 0 < X → IntegrableOn (rk F μ (Ψp o) X) Ω ν ∧
      (∫ y in Ω, rk F μ (Ψp o) X y ∂ν) = v0 * (∫ u, Ψp o u ∂μ) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, localZeta (μf i) (hp o i) 1 1 +
          c₁' * (∫ u, Ψp (some θ₀) u ∂μ) *
            ∑ p : T, deriv (fun s : ℂ => localZeta (μf p) (hp o p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, localZeta (μf i) (hp o i) 1 1) := H
  refine ⟨c₀, fun θ X hX => ?_⟩

  set M : ℂ := ∫ u, Ψ θ₀ u ∂μ with hM
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => ∏ i : T, localZeta (μf i) (h θ₀ i) 1 s := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℂ, D = ∑ p : T, deriv (fun s : ℂ => localZeta (μf p) (h θ₀ p) 1 s) 1 *
      ∏ i ∈ Finset.univ.erase p, localZeta (μf i) (h θ₀ i) 1 1 := ⟨_, rfl⟩
  have hP1 : P 1 = P0 := by rw [hP]
  have hP0 : P0 ≠ 0 := hθ₀

  have h1mem : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hPderiv : HasDerivAt P D 1 := by
    rw [hP, hD]
    refine (HasDerivAt.fun_finsetProd fun i _ =>
      ((hloc θ₀ i.1 i.2).differentiableAt (hopen.mem_nhds h1mem)).hasDerivAt).congr_deriv ?_
    beta_reduce
    exact Finset.sum_congr rfl fun p _ => by rw [smul_eq_mul, mul_comm]

  obtain ⟨e, he⟩ : ∃ e : ℂ → ℂ, e = fun s => ((((qn : ℝ))⁻¹ : ℝ) : ℂ) ^ (-s) := ⟨_, rfl⟩
  have hqinvC : ((((qn : ℝ))⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_pos.mpr hqpos).ne'
  have he1 : e 1 = ((qn : ℝ) : ℂ) := by
    rw [he]
    simp only [Complex.cpow_neg_one, Complex.ofReal_inv, inv_inv]
  have hederiv : HasDerivAt e (((qn : ℝ) : ℂ) * (Real.log (qn : ℝ) : ℂ)) 1 := by
    rw [he]
    have h := ((hasDerivAt_id' (1 : ℂ)).neg).const_cpow (c := ((((qn : ℝ))⁻¹ : ℝ) : ℂ)) (Or.inl hqinvC)
    refine h.congr_deriv ?_
    rw [show (-fun x : ℂ => x) 1 = -1 from rfl, Complex.cpow_neg_one, Complex.ofReal_inv, inv_inv, ← Complex.ofReal_inv,
      ← Complex.ofReal_log (inv_pos.mpr hqpos).le, Real.log_inv, Complex.ofReal_neg]
    ring
  have hPnone : (fun s => ∏ i : T, localZeta (μf i) (hp none i) 1 s) = fun s => e s * P s := by
    funext s
    rw [hP, he]
    simp only [hzeta_none]
    rw [Finset.prod_mul_distrib]
    congr 1
    have hfac : ∀ i : T, ((modulus ((afin : FiniteAdeleRing (𝓞 F) F) (i : HeightOneSpectrum (𝓞 F))) : ℝ) : ℂ) ^ (-s)
        = if i = ⟨p, hpT⟩ then ((((qn : ℝ))⁻¹ : ℝ) : ℂ) ^ (-s) else 1 := by
      intro i
      by_cases hi : i = ⟨p, hpT⟩
      · rw [if_pos hi, hi]
        show ((modulus ((afin : FiniteAdeleRing (𝓞 F) F) p) : ℝ) : ℂ) ^ (-s) = _
        rw [hmod_p]
      · have hip : (i : HeightOneSpectrum (𝓞 F)) ≠ p := fun h' => hi (Subtype.ext h')
        rw [if_neg hi, hmod_ne hip, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow]
    simp only [hfac]
    exact Fintype.prod_ite_eq' _ _
  have hDnone : (∑ p' : T, deriv (fun s : ℂ => localZeta (μf p') (hp none p') 1 s) 1 *
      ∏ i ∈ Finset.univ.erase p', localZeta (μf i) (hp none i) 1 1) =
        ((qn : ℝ) : ℂ) * (Real.log (qn : ℝ) : ℂ) * P 1 + ((qn : ℝ) : ℂ) * D := by

    have hloc_none : ∀ i : T, DifferentiableAt ℂ (fun s : ℂ => localZeta (μf i) (hp none i) 1 s) 1 :=
      fun i => (hloc' none i.1 i.2).differentiableAt (hopen.mem_nhds h1mem)
    have hd1 : HasDerivAt (fun s => ∏ i : T, localZeta (μf i) (hp none i) 1 s)
        (∑ p' : T, deriv (fun s : ℂ => localZeta (μf p') (hp none p') 1 s) 1 *
          ∏ i ∈ Finset.univ.erase p', localZeta (μf i) (hp none i) 1 1) 1 := by
      refine (HasDerivAt.fun_finsetProd fun i _ => (hloc_none i).hasDerivAt).congr_deriv ?_
      beta_reduce
      exact Finset.sum_congr rfl fun p _ => by rw [smul_eq_mul, mul_comm]
    have hd2 : HasDerivAt (fun s => ∏ i : T, localZeta (μf i) (hp none i) 1 s)
        (((qn : ℝ) : ℂ) * (Real.log (qn : ℝ) : ℂ) * P 1 + e 1 * D) 1 := by
      rw [hPnone]
      exact hederiv.mul hPderiv
    rw [he1] at hd2
    exact hd1.unique hd2
  have hPnone1 : (∏ i : T, localZeta (μf i) (hp none i) 1 1) = ((qn : ℝ) : ℂ) * P 1 := by
    have := congr_fun hPnone 1
    simpa only [he1] using this

  have hMa : ∫ u, Ψ θ₀ ((a : AdeleRing (𝓞 F) F) * u) ∂μ = ((ideleNorm F a : ℝ) : ℂ)⁻¹ * M :=
    integral_comp_mul_left F μ (Ψ θ₀) a
  have hMnone : (∫ u, Ψp none u ∂μ) = ((qn : ℝ) : ℂ) * M := by
    rw [hΨp_none]
    show ∫ u, Ψ θ₀ ((a : AdeleRing (𝓞 F) F) * u) ∂μ = _
    rw [hMa, ha_norm, Complex.ofReal_inv, inv_inv]
  have hMsome : (∫ u, Ψp (some θ₀) u ∂μ) = M := by rw [hΨp_some]

  have hI1 := (H' none 1 one_pos).2
  rw [hMnone, hMsome, Real.log_one, hPnone1, hDnone] at hI1

  have htrans : (∫ y in Ω, rk F μ (Ψp none) 1 y ∂ν) =
      ((qn : ℝ) : ℂ) * ∫ y in Ω, rk F μ (Ψ θ₀) (qn : ℝ) y ∂ν := by
    have hfun : rk F μ (Ψp none) 1 = fun y =>
        ((ideleNorm F a : ℝ) : ℂ)⁻¹ * rk F μ (Ψ θ₀) (1 / ideleNorm F a) (y * a⁻¹) := by
      funext y
      rw [hΨp_none]
      exact rk_comp_mul F μ (Ψ θ₀) a hMa 1 y
    rw [hfun, integral_const_mul, ha_norm, one_div, inv_inv, Complex.ofReal_inv, inv_inv,
      setIntegral_comp_mul_right F ν Ω hΩ (rk F μ (Ψ θ₀) (qn : ℝ)) (rk_smul F μ (Ψ θ₀) (qn : ℝ)) a⁻¹]
  have hIq := (H' (some θ₀) (qn : ℝ) hqpos).2
  rw [hΨp_some, hp_some, ← hD] at hIq
  have hPsome1 : (∏ i : T, localZeta (μf i) (h θ₀ i) 1 1) = P 1 := by rw [hP]
  rw [hPsome1] at hIq
  rw [htrans, hIq] at hI1
  rw [Complex.ofReal_zero, mul_zero, zero_add] at hI1
  rw [← hM] at hI1

  have hmain : c₁' * M * P 1 = v0 * M := by
    have h3 : ((qn : ℝ) : ℂ) * (Real.log (qn : ℝ) : ℂ) * (v0 * M - c₁' * M * P 1) = 0 := by
      linear_combination hI1
    have h4 : v0 * M - c₁' * M * P 1 = 0 := by
      rcases mul_eq_zero.mp h3 with h5 | h5
      · exact absurd h5 (mul_ne_zero hqC hlogq)
      · exact h5
    linear_combination -h4
  have hkey : c₁' * M = v0 / P0 * M := by
    rw [div_mul_eq_mul_div, eq_div_iff hP0, ← hP1]
    exact hmain

  refine ⟨?_, ?_⟩
  · have h1 := (H' (some θ) X hX).1
    rwa [hΨp_some] at h1
  · have h2 := (H' (some θ) X hX).2
    rw [hΨp_some, hp_some, hMsome, hkey] at h2
    exact h2

end Main

end TwistedUnipotentTerm.UniformCoefficient

end

open TwistedUnipotentTerm.UniformCoefficient in

theorem solution
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₁ : ℂ, ∀ (g : InfiniteAdeleRing F → ℂ) (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
      (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ),
      (∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
        (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x) →
      (∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) → (∀ θ, HasCompactSupport (Ψ θ)) →
    ∃ c₀ : ℂ, ∀ θ : Θ, ∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0))) Ω ν ∧
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0)) ∂ν) =
        ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
            NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, Ψ θ u ∂μ) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
          c₁ * (∫ u, Ψ θ₀ u ∂μ) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1) :=
  main F μ hμ1 ν Ω hΩ S μf T hT Θ h hloc θ₀ hθ₀

end S_TwistedUnipotentTerm_exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
end P2MW
export P2MW.S_TwistedUnipotentTerm_exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform (solution)

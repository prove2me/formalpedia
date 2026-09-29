-- Prove2me | solution 1 for TwistedUnipotentTerm.differentiableOn_localZeta_twistedLocalFactor_one_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d8299823-fa78-5bd6-8dfe-204575124d2d

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_M4aHerbrand_IdeleClassVocab

import Theorems.Thm_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn
import Theorems.Thm_LanglandsTunnell_TateLocal_differentiableOn_localZeta_one_of_continuous_of_hasCompactSupport
import Theorems.Thm_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_differentiableOn_localZeta_twistedLocalFactor_one_unram
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero"
p2m_attr_erase "simp" "LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∀ k j : ℕ, DifferentiableOn ℂ (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta μ (twistedLocalFactor K L D σ ξL v w n rT z k j) 1 s) {s : ℂ | 0 < s.re} := by
  intro k j
  classical

  have horb := TwistedUnipotentTerm.isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn K L ξL v w ϖ hϖ hϖ0 n rT hrT z hz k j

  have hloc : IsLocallyConstant (twistedLocalFactor K L D σ ξL v w n rT z k j) ∧
      HasCompactSupport (twistedLocalFactor K L D σ ξL v w n rT z k j) := by
    letI mK : ∀ u : HeightOneSpectrum (𝓞 K), MeasurableSpace (u.adicCompletion K) := fun u => borel _
    haveI bK : ∀ u : HeightOneSpectrum (𝓞 K), BorelSpace (u.adicCompletion K) := fun u => ⟨rfl⟩
    obtain ⟨S₀, hS₀⟩ :=
      @TraceFibrePushforward.exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator K L _ _ _ _ _ mK bK
    obtain ⟨gK, hgK⟩ := hS₀ (fun _ => 0) continuous_const
      (HasCompactSupport.zero : HasCompactSupport (0 : InfiniteAdeleRing L → ℂ))
    let Fv : (u : HeightOneSpectrum (𝓞 K)) → L ⊗[K] u.adicCompletion K → ℂ :=
      Function.update (fun u _ => 0) v (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j)
    have hFv : Fv v = TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j :=
      Function.update_self v _ (fun u (_ : L ⊗[K] u.adicCompletion K) => (0 : ℂ))
    obtain ⟨-, hall⟩ := hgK (insert v S₀) Fv
      (fun x => (AutomorphicForm.AdelicTracePushforward.semiLocalIntegralOutside K L (insert v S₀)).indicator
        (fun x => (fun _ : InfiniteAdeleRing L => (0 : ℂ)) x.1 *
          ∏ u ∈ insert v S₀, Fv u (AutomorphicForm.semiLocalEval K L u x.2)) x)
      (Finset.subset_insert v S₀) (fun _ => rfl) (by
        intro u hu
        by_cases huv : u = v
        · subst huv
          rw [hFv]
          exact horb
        · have h0 : Fv u = fun _ => 0 := Function.update_of_ne huv _ _
          rw [h0]
          open scoped TensorProduct.RightActions in
          exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩)
    have hv := hall v (Finset.mem_insert_self v S₀)
    rw [hFv] at hv
    exact hv

  exact LanglandsTunnell.TateLocal.differentiableOn_localZeta_one_of_continuous_of_hasCompactSupport K v μ _ hloc.1.continuous hloc.2

end S_TwistedUnipotentTerm_differentiableOn_localZeta_twistedLocalFactor_one_unram
end P2MW
export P2MW.S_TwistedUnipotentTerm_differentiableOn_localZeta_twistedLocalFactor_one_unram (solution)

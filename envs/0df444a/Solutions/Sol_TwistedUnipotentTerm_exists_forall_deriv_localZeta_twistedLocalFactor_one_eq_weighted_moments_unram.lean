-- Prove2me | solution 1 for TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d76b37cb-22f2-5788-835b-d512af6d9423

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_M4aHerbrand_IdeleClassVocab

import Theorems.Thm_TwistedUnipotentTerm_exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
import Theorems.Thm_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn
import Theorems.Thm_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
import Theorems.Thm_HeckeTreeWalk_cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow
import Theorems.Thm_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow
import Theorems.Thm_LanglandsTunnell_TateLocal_hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport
import Theorems.Thm_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus
import Theorems.Thm_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
import Theorems.Thm_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero"
p2m_attr_erase "simp" "LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

namespace C3aAux

def walkW (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (q + 1) * walkW q k 1
  | k + 1, d + 1 => walkW q k d + q * walkW q k (d + 2)

theorem walkW_zero_zero (q : ℕ) : walkW q 0 0 = 1 := rfl
theorem walkW_zero_succ (q d : ℕ) : walkW q 0 (d + 1) = 0 := rfl
theorem walkW_succ_zero (q k : ℕ) : walkW q (k + 1) 0 = (q + 1) * walkW q k 1 := rfl
theorem walkW_succ_succ (q k d : ℕ) : walkW q (k + 1) (d + 1) = walkW q k d + q * walkW q k (d + 2) := rfl

theorem walkW_eq_zero (q : ℕ) : ∀ k d : ℕ, k < d → walkW q k d = 0 := by
  intro k
  induction k with
  | zero =>
    intro d hd
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rfl
  | succ k ih =>
    intro d hd
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [walkW_succ_succ, ih d (by omega), ih (d + 2) (by omega), mul_zero, add_zero]

theorem centralBinom_eq_four_pow_mul_prod (m : ℕ) :
    (((2 * m).choose m : ℕ) : ℝ) = 4 ^ m * ∏ n ∈ Finset.range m, (2 * (n : ℝ) + 1) / (2 * n + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, pow_succ]
    have h := Nat.succ_mul_centralBinom_succ m
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
    have h' : (((2 * (m + 1)).choose (m + 1) : ℕ) : ℝ) =
        2 * (2 * m + 1) / (m + 1) * (((2 * m).choose m : ℕ) : ℝ) := by
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      have := congrArg (Nat.cast : ℕ → ℝ) h
      push_cast at this
      linarith
    rw [h', ih]
    have hm : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
    have hm' : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem collapse (N p M ℓ W0 X Y C Q P4 : ℂ) (hN : N - 1 ≠ 0) (hp : p - 1 ≠ 0)
    (hV : W0 + X = C * Q) (hD : 2 * ((N - 1) * Y - W0) = (N - 1) * P4 - (N + 1) * C * Q) :
    M * ℓ * (-W0 / (p - 1) + (Y - (1 / (p - 1) - 1 / (N - 1)) * X)) =
      M * ℓ / 2 * P4 - M * ℓ * ((N + 1) / (2 * (N - 1)) + (1 / (p - 1) - 1 / (N - 1))) * (C * Q) := by
  have hX : X = C * Q - W0 := by linear_combination hV
  have hY : Y = ((N - 1) * P4 - (N + 1) * C * Q + 2 * W0) / (2 * (N - 1)) := by
    field_simp
    linear_combination hD
  rw [hX, hY]
  field_simp
  ring

end C3aAux

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1)
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
    ∃ e₁ e₂ : ℂ, ∀ k j : ℕ,
      deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta μ (twistedLocalFactor K L D σ ξL v w n rT z k j) 1 s) 1 =
        e₁ * ((1 + (-1 : ℂ) ^ k) * (4 * (AutomorphicForm.HeckeEigensystem.cNorm w.1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) +
        e₂ * ((1 + (-1 : ℂ) ^ k) / 2 * (4 * (AutomorphicForm.HeckeEigensystem.cNorm w.1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) *
            ((∏ n ∈ Finset.range (k / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) := by
  classical

  obtain ⟨hKv⟩ := (inferInstance : BorelSpace (v.adicCompletion K))
  subst hKv
  letI mKv : MeasurableSpace (v.adicCompletion K) := borel _
  haveI hBK : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

  open scoped TensorProduct.RightActions in
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  open scoped TensorProduct.RightActions in
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  open scoped TensorProduct.RightActions in
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  open scoped TensorProduct.RightActions in
  letI mT : MeasurableSpace (L ⊗[K] v.adicCompletion K) := borel _
  open scoped TensorProduct.RightActions in
  haveI bT : BorelSpace (L ⊗[K] v.adicCompletion K) := ⟨rfl⟩

  open scoped TensorProduct.RightActions in
  obtain ⟨cB, hcB, hB⟩ :=
    AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
      K L v μ (MeasureTheory.Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K))
  have hlog := LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus K v μ
  have hlogC : LocallyIntegrable
      (fun y : v.adicCompletion K => ((Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ) : ℝ) : ℂ)) μ := by
    intro x
    obtain ⟨s, hs, hi⟩ := hlog x
    exact ⟨s, hs, hi.ofReal⟩

  set q : ℕ := Ideal.absNorm w.1.asIdeal with hq
  set p : ℕ := Ideal.absNorm v.asIdeal with hp
  obtain ⟨V, hV, hA⟩ :=
    TwistedUnipotentTerm.exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
      K L ξL v w hξv ϖ hϖ hϖ0 n rT hrT z hz (C3aAux.walkW q) (C3aAux.walkW_zero_zero q)
      (C3aAux.walkW_zero_succ q) (C3aAux.walkW_succ_zero q) (C3aAux.walkW_succ_succ q)
  have h70 := HeckeTreeWalk.cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow q
    (C3aAux.walkW q) (C3aAux.walkW_zero_zero q) (C3aAux.walkW_zero_succ q) (C3aAux.walkW_succ_zero q)
    (C3aAux.walkW_succ_succ q)
  have hCD := HeckeTreeWalk.two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow q
    (C3aAux.walkW q) (C3aAux.walkW_zero_zero q) (C3aAux.walkW_zero_succ q) (C3aAux.walkW_succ_zero q)
    (C3aAux.walkW_succ_succ q)

  open scoped TensorProduct.RightActions in
  set M : ℂ := (((MeasureTheory.Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K))
      {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L),
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}).toReal : ℂ)
    with hM
  set ℓ : ℂ := ((Real.log (p : ℝ) : ℝ) : ℂ) with hℓ
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    have : p ≠ 1 := fun h1 => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp (hp ▸ h1))
    exact_mod_cast this
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    have : q ≠ 1 := fun h1 => w.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp (hq ▸ h1))
    exact_mod_cast this
  refine ⟨(cB : ℂ) * V * (M * ℓ) / 4,
    -((cB : ℂ) * V * (M * ℓ * (((q : ℂ) + 1) / (2 * ((q : ℂ) - 1)) + (1 / ((p : ℂ) - 1) - 1 / ((q : ℂ) - 1))))),
    fun k j => ?_⟩

  have horb := TwistedUnipotentTerm.isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn
    K L ξL v w ϖ hϖ hϖ0 n rT hrT z hz k j
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

  rw [(LanglandsTunnell.TateLocal.hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport
    K v μ _ hloc.1.continuous hloc.2).deriv]
  have hF : twistedLocalFactor K L D σ ξL v w n rT z k j =
      AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v
        (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j) := rfl
  rw [hF]
  obtain ⟨-, -, hBeq⟩ := hB (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j)
    (fun y : v.adicCompletion K => ((Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ) : ℝ) : ℂ))
    horb.1 horb.2 hlogC
  rw [hBeq]

  rw [show TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j = fun x =>
      V * ((1 + (-1 : ℂ) ^ k) / 2 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (k / 2 + j)) *
      {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
          HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
            w'.1.adicCompletionIntegers L}.indicator
        (fun x => (C3aAux.walkW q k (2 * (WithZero.log (Valued.v
          (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) : ℂ)) x
      from funext (hA k j)]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  open scoped TensorProduct.RightActions in
  obtain ⟨-, hS⟩ := TwistedUnipotentTerm.integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
    K L v w hunr (MeasureTheory.Measure.addHaar : Measure (L ⊗[K] v.adicCompletion K))
    (fun r => (C3aAux.walkW q k (2 * r) : ℂ)) (k / 2)
    (fun r hr => by
      show ((C3aAux.walkW q k (2 * r) : ℕ) : ℂ) = 0
      rw [C3aAux.walkW_eq_zero q k (2 * r) (by omega), Nat.cast_zero])
  rw [hS]
  rw [← hp, ← hq]
  rw [← hℓ, ← hM]

  have hcN : AutomorphicForm.HeckeEigensystem.cNorm w.1 = (q : ℂ) := by
    simp [AutomorphicForm.HeckeEigensystem.cNorm, hq]
  rw [hcN]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  ·
    have hk2 : (m + m) / 2 = m := by omega
    have hpar : (1 + (-1 : ℂ) ^ (m + m)) / 2 = 1 := by
      rw [Even.neg_one_pow ⟨m, rfl⟩]; norm_num
    have hpar' : (1 + (-1 : ℂ) ^ (m + m)) = 2 := by
      rw [Even.neg_one_pow ⟨m, rfl⟩]; norm_num
    rw [hk2]
    simp only [mul_zero]

    have h70m := congrArg (Int.cast : ℤ → ℂ) (h70 m)
    have hCDm := congrArg (Int.cast : ℤ → ℂ) (hCD m)
    push_cast at h70m hCDm
    rw [show 2 * m = m + m from two_mul m] at h70m hCDm

    set X : ℂ := ∑ r ∈ Finset.Icc 1 m, ((C3aAux.walkW q (m + m) (2 * r) : ℕ) : ℂ) *
        ((q : ℂ) ^ r - (q : ℂ) ^ (r - 1)) with hX
    set Y : ℂ := ∑ r ∈ Finset.Icc 1 m, (r : ℂ) * ((C3aAux.walkW q (m + m) (2 * r) : ℕ) : ℂ) *
        ((q : ℂ) ^ r - (q : ℂ) ^ (r - 1)) with hY
    have hsplit : ∑ r ∈ Finset.Icc 1 m, ((C3aAux.walkW q (m + m) (2 * r) : ℕ) : ℂ) *
          ((q : ℂ) ^ r - (q : ℂ) ^ (r - 1)) *
            ((r : ℂ) - 1 / ((p : ℂ) - 1) + 1 / ((q : ℂ) - 1)) =
        Y - (1 / ((p : ℂ) - 1) - 1 / ((q : ℂ) - 1)) * X := by
      rw [hY, hX, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [hsplit]
    have hcol := C3aAux.collapse (q : ℂ) (p : ℂ) M ℓ (((C3aAux.walkW q (m + m) 0 : ℕ) : ℂ)) X Y
      (((m + m).choose m : ℕ) : ℂ) ((q : ℂ) ^ m) ((4 * (q : ℂ)) ^ m) hq1 hp1 h70m hCDm
    have hbin := C3aAux.centralBinom_eq_four_pow_mul_prod m
    rw [two_mul] at hbin
    have hbinC : (((m + m).choose m : ℕ) : ℂ) =
        (4 : ℂ) ^ m * ((∏ n ∈ Finset.range m, (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) := by
      have := congrArg (Complex.ofReal) hbin
      push_cast at this ⊢
      exact this
    rw [hpar, hpar']
    rw [hbinC] at hcol

    linear_combination ((cB : ℂ) * V * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m + j)) * hcol
  ·
    have hpar : (1 + (-1 : ℂ) ^ (2 * m + 1)) / 2 = 0 := by
      rw [Odd.neg_one_pow ⟨m, rfl⟩]; norm_num
    have hpar' : (1 + (-1 : ℂ) ^ (2 * m + 1)) = 0 := by
      rw [Odd.neg_one_pow ⟨m, rfl⟩]; norm_num
    rw [hpar, hpar']
    ring

end S_TwistedUnipotentTerm_exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
end P2MW
export P2MW.S_TwistedUnipotentTerm_exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram (solution)

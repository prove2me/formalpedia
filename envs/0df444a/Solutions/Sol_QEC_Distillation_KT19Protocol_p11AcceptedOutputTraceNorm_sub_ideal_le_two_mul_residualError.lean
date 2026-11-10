-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.p11AcceptedOutputTraceNorm_sub_ideal_le_two_mul_residualError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:45:05.686229+00:00
-- url     : https://prove2.me/submissions/a9a0137d-21fb-4d3a-a6e0-50c7b321cd6b

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19DecoderChannel_rankOne_encoded
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19EndpointCompletion_eq_conditional_of_pos
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19Success_eq_acceptedWord_sum
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19Success_pos_of_errorRate_lt_one
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19AcceptedEndpointWeight_pos_of_errorRate_lt_one
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_FiniteCentering_finset_centered_sum_eq_nonzero_residual
import Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_finset_weighted_residual_traceNorm_le_two_mul_mass
import Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_normalized_residual_traceNorm_le
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cosetKet_apply
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cosetLabel_eq_combinedWord
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_traceNorm_eq_one
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_branchOperator_accepted
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_smul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_sum
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply
section
noncomputable section
namespace QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
section Syndromes
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
private theorem kt19RowCarrier_mem_iff_exists_cosetLabel
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) :
    word ∈ rowCarrier R ↔
      ∃ logical : Logical → ZMod q, ∃ stabilizer : Stabilizer → ZMod q,
        R.cosetLabel logical stabilizer = word := by
  classical
  constructor
  · intro hword
    obtain ⟨coefficient, hcoefficient⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod q)).mp hword
    change R.combinedWord coefficient = word at hcoefficient
    let logical : Logical → ZMod q := fun index => -coefficient (Sum.inl index)
    let stabilizer : Stabilizer → ZMod q := fun index => coefficient (Sum.inr index)
    refine ⟨logical, stabilizer, ?_⟩
    have hcoefficient_eq :
        CubicRowFamily.combinedCoefficient logical stabilizer = coefficient := by
      funext row
      rcases row with index | index
      · simp [logical, CubicRowFamily.combinedCoefficient]
      · simp [stabilizer, CubicRowFamily.combinedCoefficient]
    rw [R.cosetLabel_eq_combinedWord, hcoefficient_eq, hcoefficient]
  · rintro ⟨logical, stabilizer, hlabel⟩
    apply (Submodule.mem_span_range_iff_exists_fun (ZMod q)).mpr
    refine ⟨CubicRowFamily.combinedCoefficient logical stabilizer, ?_⟩
    change R.combinedWord (CubicRowFamily.combinedCoefficient logical stabilizer) = word
    rw [← R.cosetLabel_eq_combinedWord]
    exact hlabel
private theorem kt19CharacterKet_zero_apply
    (word : PrimeQuditRegisterLabel q Site) :
    characterKet q 0 word =
      (Real.sqrt (q : Real) : Complex)⁻¹ ^ Fintype.card Site := by
  rw [characterKet_apply]
  simp [registerPairing]
private theorem kt19CosetNormalization_ne_zero
    (R : CubicRowFamily q Logical Stabilizer Site) :
    CubicRowFamily.cosetNormalization q Stabilizer ≠ 0 := by
  intro hzero
  have hunit := R.cosetNormalization_conj_mul_card
  rw [hzero] at hunit
  norm_num at hunit
private theorem kt19CosetKet_apply_of_cosetLabel
    (R : CubicRowFamily q Logical Stabilizer Site)
    (logical : Logical → ZMod q) (stabilizer : Stabilizer → ZMod q) :
    (R.cosetKet logical).ofLp (R.cosetLabel logical stabilizer) =
      CubicRowFamily.cosetNormalization q Stabilizer := by
  simpa [registerBasisKet, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left] using
    R.cosetKet_apply logical stabilizer
private theorem kt19CosetKet_apply_eq_zero_of_not_mem
    (R : CubicRowFamily q Logical Stabilizer Site)
    (logical : Logical → ZMod q) (word : PrimeQuditRegisterLabel q Site)
    (hword : ∀ stabilizer : Stabilizer → ZMod q,
      R.cosetLabel logical stabilizer ≠ word) :
    (R.cosetKet logical).ofLp word = 0 := by
  classical
  unfold CubicRowFamily.cosetKet
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro stabilizer _
  have hne := hword stabilizer
  have hne' : word ≠ R.cosetLabel logical stabilizer := Ne.symm hne
  simp [registerBasisKet, EuclideanSpace.basisFun_apply, hne, hne']
private theorem kt19Encoding_characterKet_zero_apply
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) :
    R.encodingLinearMap (characterKet q 0) word =
      if word ∈ rowCarrier R then
        CubicRowFamily.cosetNormalization q Stabilizer *
          ((Real.sqrt (q : Real) : Complex)⁻¹ ^ Fintype.card Logical)
      else 0 := by
  classical
  by_cases hword : word ∈ rowCarrier R
  · obtain ⟨logical, stabilizer, hlabel⟩ :=
      (kt19RowCarrier_mem_iff_exists_cosetLabel R word).mp hword
    rw [if_pos hword]
    change (∑ logical : Logical → ZMod q,
      characterKet q 0 logical • R.cosetKet logical).ofLp word = _
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [Finset.sum_eq_single logical]
    · rw [← hlabel, kt19CosetKet_apply_of_cosetLabel R logical stabilizer,
        kt19CharacterKet_zero_apply (q := q) (Site := Logical) logical]
      ring
    · intro other _ hother
      have hnot : ∀ stabilizer' : Stabilizer → ZMod q,
          R.cosetLabel other stabilizer' ≠ word := by
        intro stabilizer' heq
        apply hother
        exact R.cosetLabel_eq_implies_logical_eq other logical stabilizer'
          stabilizer (heq.trans hlabel.symm)
      rw [kt19CosetKet_apply_eq_zero_of_not_mem R other word hnot]
      simp
    · simp
  · rw [if_neg hword]
    change (∑ logical : Logical → ZMod q,
      characterKet q 0 logical • R.cosetKet logical).ofLp word = 0
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro logical _
    have hnot : ∀ stabilizer : Stabilizer → ZMod q,
        R.cosetLabel logical stabilizer ≠ word := by
      intro stabilizer heq
      apply hword
      exact (kt19RowCarrier_mem_iff_exists_cosetLabel R word).mpr
        ⟨logical, stabilizer, heq⟩
    rw [kt19CosetKet_apply_eq_zero_of_not_mem R logical word hnot]
    simp
private theorem kt19DecoderEncodingIsometry_magicRegisterKet_zero
    (R : CubicRowFamily q Logical Stabilizer Site) :
    kt19DecoderEncodingIsometry R (magicRegisterKet q 0) =
      physicalU13 q (R.encodingLinearMap (characterKet q 0)) := by
  change physicalU13 q
      (R.encodingLinearMap ((physicalU13 q).symm (magicRegisterKet q 0))) = _
  rw [inverseTransversal_magicRegisterKet]
private theorem kt19ZeroWord_sector_is_encoded
    (R : CubicRowFamily q Logical Stabilizer Site) :
    ∃ scale : Complex,
      physicalU13 q (zSyndromeProjector R 0 (characterKet q 0)) =
        scale • kt19DecoderEncodingIsometry R (magicRegisterKet q 0) := by
  let physicalAmplitude : Complex :=
    (Real.sqrt (q : Real) : Complex)⁻¹ ^ Fintype.card Site
  let encodedAmplitude : Complex :=
    CubicRowFamily.cosetNormalization q Stabilizer *
      ((Real.sqrt (q : Real) : Complex)⁻¹ ^ Fintype.card Logical)
  have hqpos : (0 : Real) < (q : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsqrt : (Real.sqrt (q : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hqpos
  have hlogicalAmplitude :
      ((Real.sqrt (q : Real) : Complex)⁻¹ ^ Fintype.card Logical) ≠ 0 := by
    exact pow_ne_zero _ (inv_ne_zero hsqrt)
  have hencodedAmplitude : encodedAmplitude ≠ 0 := by
    dsimp [encodedAmplitude]
    exact mul_ne_zero (kt19CosetNormalization_ne_zero R) hlogicalAmplitude
  let scale : Complex := physicalAmplitude * encodedAmplitude⁻¹
  have hscale_encoded : scale * encodedAmplitude = physicalAmplitude := by
    calc
      scale * encodedAmplitude =
          (physicalAmplitude * encodedAmplitude⁻¹) * encodedAmplitude := by rfl
      _ = physicalAmplitude * (encodedAmplitude⁻¹ * encodedAmplitude) := by
        rw [mul_assoc]
      _ = physicalAmplitude := by
        rw [inv_mul_cancel₀ hencodedAmplitude, mul_one]
  have hprojector :
      zSyndromeProjector R 0 (characterKet q 0) =
        scale • R.encodingLinearMap (characterKet q 0) := by
    ext word
    change (zSyndromeProjector R 0 (characterKet q 0)).ofLp word =
      (scale • R.encodingLinearMap (characterKet q 0)).ofLp word
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hword : word ∈ rowCarrier R
    · have hsector : zSyndrome R word = 0 :=
        (zSyndrome_eq_zero_iff_mem_rowCarrier R word).mpr hword
      rw [zSyndromeProjector_apply, if_pos hsector,
        kt19Encoding_characterKet_zero_apply R word, if_pos hword,
        kt19CharacterKet_zero_apply]
      simpa [physicalAmplitude, encodedAmplitude] using hscale_encoded.symm
    · have hsector : zSyndrome R word ≠ 0 := by
        intro hzero
        exact hword ((zSyndrome_eq_zero_iff_mem_rowCarrier R word).mp hzero)
      rw [zSyndromeProjector_apply, if_neg hsector,
        kt19Encoding_characterKet_zero_apply R word, if_neg hword]
      simp
  refine ⟨scale, ?_⟩
  rw [hprojector, map_smul,
    ← kt19DecoderEncodingIsometry_magicRegisterKet_zero]
private theorem kt19ZeroWord_xSyndrome
    (R : CubicRowFamily q Logical Stabilizer Site) :
    xSyndrome R (0 : PrimeQuditRegisterLabel q Site) = 0 := by
  funext index
  simp [xSyndrome, wordPairing_apply, dotProduct]
private theorem kt19ZeroWord_success_mass
    (R : CubicRowFamily q Logical Stabilizer Site) :
    kt19WordSuccessMass R 0 = 1 := by
  rw [kt19WordSuccessMass_eq_ite_acceptedWord]
  simp [kt19AcceptedWord, kt19ZeroWord_xSyndrome]
private theorem kt19ZeroWord_accepted_branchOperator_eq_sum
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) 0).toOperator =
      ∑ syndrome : ZSyndrome R,
        (InnerProductSpace.rankOne Complex
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q 0)))
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q 0)))).toLinearMap := by
  classical
  rw [kt19DistillationInstrument,
    FiniteInstrument.binaryCoarsen_branchOperator_accepted,
    Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [Finset.sum_eq_single (0 : Stabilizer → ZMod q)]
  · rw [kt19ProtocolInstrument_branchOperator_wordInputDensity R syndrome 0 0]
    simp [kt19Accepts, kt19ZeroWord_xSyndrome, registerPairing]
  · intro other _ hother
    simp [kt19Accepts, hother]
  · simp
private theorem kt19RankOne_smul_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (scalar : Complex) (psi : H) :
    (InnerProductSpace.rankOne Complex (scalar • psi) (scalar • psi)).toLinearMap =
      (star scalar * scalar) •
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  simp [InnerProductSpace.rankOne_apply]
  rw [smul_smul, mul_comm scalar]
private theorem kt19ZeroWord_decodedAccepted_eq_ideal
    (R : CubicRowFamily q Logical Stabilizer Site) :
    kt19DecoderChannel R
      ((kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) 0).toOperator) =
      (kt19IdealOutput (q := q) (Logical := Logical)).toOperator := by
  classical
  let raw : Operator (PrimeQuditRegister q Site) :=
    (kt19DistillationInstrument R).branchOperator .accepted
      (kt19WordInputDensity (Site := Site) 0).toOperator
  obtain ⟨scale, hsector⟩ := kt19ZeroWord_sector_is_encoded R
  let coefficient : Complex := ∑ _syndrome : ZSyndrome R, star scale * scale
  have hraw : raw =
      ∑ syndrome : ZSyndrome R,
        (InnerProductSpace.rankOne Complex
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q 0)))
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q 0)))).toLinearMap := by
    simpa [raw] using kt19ZeroWord_accepted_branchOperator_eq_sum R
  have hdecoded : kt19DecoderChannel R raw =
      coefficient • (kt19IdealOutput (q := q) (Logical := Logical)).toOperator := by
    rw [hraw, map_sum]
    simp_rw [hsector, kt19RankOne_smul_self, map_smul,
      kt19DecoderChannel_rankOne_encoded]
    simp only [kt19IdealOutput, DensityOperator.pureDensity_toOperator]
    dsimp [coefficient]
    rw [Finset.sum_smul]
  have hraw_trace :
      LinearMap.trace Complex (PrimeQuditRegister q Site) raw = 1 := by
    change LinearMap.trace Complex (PrimeQuditRegister q Site)
      ((kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) 0).toOperator) = 1
    rw [(kt19DistillationInstrument R).trace_branchOperator_eq_bornWeight
      .accepted (kt19WordInputDensity (Site := Site) 0)]
    simpa [kt19WordSuccessMass] using
      congrArg (fun value : ℝ => (value : Complex)) (kt19ZeroWord_success_mass R)
  have hdecoded_trace :
      LinearMap.trace Complex (PrimeQuditRegister q Logical)
        (kt19DecoderChannel R raw) = 1 := by
    rw [(kt19DecoderChannel R).trace_map]
    exact hraw_trace
  have hcoefficient : coefficient = 1 := by
    rw [hdecoded, map_smul, kt19IdealOutput,
      DensityOperator.pureDensity_toOperator, InnerProductSpace.trace_rankOne,
      magicRegisterKet_inner_self] at hdecoded_trace
    simpa using hdecoded_trace
  change kt19DecoderChannel R raw =
    (kt19IdealOutput (q := q) (Logical := Logical)).toOperator
  rw [hdecoded, hcoefficient, one_smul]
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
private theorem kt19RawAcceptedEndpoint_eq_acceptedWord_sum
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    kt19RawEndpoint R mu hmu_nonneg hmu_sum .accepted =
      ∑ error : PrimeQuditRegisterLabel q Site,
        if kt19AcceptedWord R error then
          (wordProbability q mu error : Complex) •
            (kt19DistillationInstrument R).branchOperator .accepted
              (kt19WordInputDensity (Site := Site) error).toOperator
        else 0 := by
  classical
  unfold kt19RawEndpoint kt19IIDResource
  rw [magicRegisterResource, DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  rw [FiniteInstrument.branchOperator_sum]
  simp_rw [FiniteInstrument.branchOperator_smul]
  apply Finset.sum_congr rfl
  intro error _
  change (wordProbability q mu error : Complex) •
      (kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) error).toOperator = _
  by_cases haccepted : kt19AcceptedWord R error
  · simp [haccepted]
  · have hsyndrome : xSyndrome R error ≠ 0 := by
      simpa [kt19AcceptedWord] using haccepted
    rw [kt19DistillationInstrument_accepted_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_ne_zero
      R error hsyndrome]
    simp [haccepted]
private theorem kt19AcceptedDecodedBranch_of_accepted
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error) :
    kt19AcceptedDecodedBranch R error =
      kt19DecoderChannel R
        ((kt19DistillationInstrument R).branchOperator .accepted
          (kt19WordInputDensity (Site := Site) error).toOperator) := by
  simp [kt19AcceptedDecodedBranch, haccepted]
private theorem kt19AcceptedDecodedBranch_zero_eq_ideal
    (R : CubicRowFamily q Logical Stabilizer Site) :
    kt19AcceptedDecodedBranch R (0 : PrimeQuditRegisterLabel q Site) =
      (kt19IdealOutput (q := q) (Logical := Logical)).toOperator := by
  have haccepted : kt19AcceptedWord R (0 : PrimeQuditRegisterLabel q Site) := by
    simp [kt19AcceptedWord, kt19ZeroWord_xSyndrome]
  rw [kt19AcceptedDecodedBranch, if_pos haccepted]
  exact kt19ZeroWord_decodedAccepted_eq_ideal R
private theorem kt19DecodedRawAcceptedEndpoint_eq_acceptedWord_sum
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    kt19DecoderChannel R (kt19RawEndpoint R mu hmu_nonneg hmu_sum .accepted) =
      ∑ error : PrimeQuditRegisterLabel q Site,
        if kt19AcceptedWord R error then
          (wordProbability q mu error : Complex) • kt19AcceptedDecodedBranch R error
        else 0 := by
  rw [kt19RawAcceptedEndpoint_eq_acceptedWord_sum R mu hmu_nonneg hmu_sum, map_sum]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccepted : kt19AcceptedWord R error
  · rw [if_pos haccepted, map_smul,
      kt19AcceptedDecodedBranch_of_accepted R error haccepted]
    simp [haccepted]
  · simp [haccepted]
private theorem kt19Success_cast_eq_acceptedWord_sum
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19Success R mu hmu_nonneg hmu_sum : Complex) =
      ∑ error : PrimeQuditRegisterLabel q Site,
        if kt19AcceptedWord R error then (wordProbability q mu error : Complex) else 0 := by
  rw [kt19Success_eq_acceptedWord_sum R mu hmu_nonneg hmu_sum,
    Finset.sum_filter, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccepted : kt19AcceptedWord R error <;> simp [haccepted]
private theorem kt19AcceptedDecodedDensity_toOperator
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error) :
    (kt19AcceptedDecodedDensity R error haccepted).toOperator =
      kt19AcceptedDecodedBranch R error := by
  rw [kt19AcceptedDecodedBranch_of_accepted R error haccepted]
  unfold kt19AcceptedDecodedDensity
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteInstrument.conditionalDensity_toOperator]
  change kt19DecoderChannel R
      ((kt19WordSuccessMass R error : Complex)⁻¹ •
        (kt19DistillationInstrument R).branchOperator .accepted
          (kt19WordInputDensity (Site := Site) error).toOperator) = _
  rw [map_smul, kt19WordSuccessMass_eq_ite_acceptedWord, if_pos haccepted]
  simp
private theorem kt19AcceptedDecodedBranch_traceNorm_sub_ideal_le_two
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) :
    traceNorm (kt19AcceptedDecodedBranch R error -
      (kt19IdealOutput (q := q) (Logical := Logical)).toOperator) ≤ 2 := by
  classical
  by_cases haccepted : kt19AcceptedWord R error
  · rw [← kt19AcceptedDecodedDensity_toOperator R error haccepted]
    calc
      traceNorm ((kt19AcceptedDecodedDensity R error haccepted).toOperator -
          (kt19IdealOutput (q := q) (Logical := Logical)).toOperator) ≤
          traceNorm (kt19AcceptedDecodedDensity R error haccepted).toOperator +
            traceNorm (-(kt19IdealOutput (q := q) (Logical := Logical)).toOperator) := by
        simpa [sub_eq_add_neg] using
          traceNorm_add_le (kt19AcceptedDecodedDensity R error haccepted).toOperator
            (-(kt19IdealOutput (q := q) (Logical := Logical)).toOperator)
      _ = 2 := by
        rw [DensityOperator.traceNorm_eq_one, traceNorm_neg,
          DensityOperator.traceNorm_eq_one]
        norm_num
  · rw [kt19AcceptedDecodedBranch, if_neg haccepted]
    rw [sub_self, (traceNorm_eq_zero_iff
      (0 : Operator (PrimeQuditRegister q Logical))).mpr rfl]
    norm_num
private theorem p11DecodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1) :
    kt19DecoderChannel p11CubicRowFamily
        (kt19RawEndpoint p11CubicRowFamily mu hmu_nonneg hmu_sum .accepted) -
      (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum : Complex) •
        (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator =
      p11AcceptedResidualDecodedDifference mu := by
  rw [kt19DecodedRawAcceptedEndpoint_eq_acceptedWord_sum p11CubicRowFamily
      mu hmu_nonneg hmu_sum,
    kt19Success_cast_eq_acceptedWord_sum p11CubicRowFamily mu hmu_nonneg hmu_sum]
  unfold p11AcceptedResidualDecodedDifference
  exact FiniteCentering.finset_centered_sum_eq_nonzero_residual
    (Finset.univ : Finset (Word (ZMod 11) (KeptPunctureLocation 11 2)))
    (fun error => (wordProbability 11 mu error : Complex))
    (kt19AcceptedWord p11CubicRowFamily)
    (kt19AcceptedDecodedBranch p11CubicRowFamily)
    0
    (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator
    (kt19AcceptedDecodedBranch_zero_eq_ideal p11CubicRowFamily)
private theorem p11AcceptedResidualDecodedDifference_traceNorm_le_two_mul_mass
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a) :
    traceNorm (p11AcceptedResidualDecodedDifference mu) ≤
      2 * p11AcceptedResidualMass mu := by
  unfold p11AcceptedResidualDecodedDifference
  calc
    traceNorm (∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
        if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
          (wordProbability 11 mu error : Complex) •
            (kt19AcceptedDecodedBranch p11CubicRowFamily error -
              (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator)
        else 0) ≤
        ∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
          if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
            2 * wordProbability 11 mu error
          else 0 := by
      simpa using
        (FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
          (Finset.univ : Finset (Word (ZMod 11) (KeptPunctureLocation 11 2)))
          (wordProbability 11 mu)
          (fun error => kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0)
          (kt19AcceptedDecodedBranch p11CubicRowFamily)
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator
          (fun error => wordProbability_nonneg 11 mu hmu_nonneg error)
          (fun error =>
            kt19AcceptedDecodedBranch_traceNorm_sub_ideal_le_two
              p11CubicRowFamily error))
    _ = 2 * p11AcceptedResidualMass mu := by
      unfold p11AcceptedResidualMass
      calc
        (∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
            if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
              2 * wordProbability 11 mu error
            else 0) =
            ∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
              2 * (if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
                wordProbability 11 mu error
              else 0) := by
          apply Finset.sum_congr rfl
          intro error _
          by_cases hresidual : kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 <;>
            simp [hresidual]
        _ = 2 * ∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
            if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
              wordProbability 11 mu error
            else 0 := by
          rw [← Finset.mul_sum]
private theorem p11AcceptedOutput_sub_ideal_eq_normalizedResidual
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    (kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput.toOperator -
        (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator =
      (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ •
        p11AcceptedResidualDecodedDifference mu := by
  have hsuccess :
      0 < kt19EndpointWeight p11CubicRowFamily mu hmu_nonneg hmu_sum .accepted :=
    kt19AcceptedEndpointWeight_pos_of_errorRate_lt_one
      p11CubicRowFamily mu hmu_nonneg hmu_sum heps
  rw [kt19Run_acceptedOutput,
    kt19EndpointCompletion_eq_conditional_of_pos
      p11CubicRowFamily mu hmu_nonneg hmu_sum .accepted hsuccess]
  dsimp only [kt19EndpointWeight] at hsuccess
  unfold kt19EndpointConditional
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteInstrument.conditionalDensity_toOperator]
  rw [map_smul]
  change
    (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ •
        kt19DecoderChannel p11CubicRowFamily
          (kt19RawEndpoint p11CubicRowFamily mu hmu_nonneg hmu_sum .accepted) -
      (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator = _
  have hrewrite :
      (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ •
          kt19DecoderChannel p11CubicRowFamily
            (kt19RawEndpoint p11CubicRowFamily mu hmu_nonneg hmu_sum .accepted) -
        (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator =
      (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ •
        p11AcceptedResidualDecodedDifference mu := by
    rw [← p11DecodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
      mu hmu_nonneg hmu_sum]
    have hne : (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (kt19Success_pos_of_errorRate_lt_one
        p11CubicRowFamily mu hmu_nonneg hmu_sum heps))
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact hrewrite
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
end Syndromes
end QEC.Distillation.KT19Protocol
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime
attribute [local instance] QEC.Distillation.KT19Protocol.p11NeZero
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
namespace QEC.Distillation.KT19Protocol
theorem _root_.solution
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    traceNorm ((kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput.toOperator -
      (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) ≤
      2 * p11AcceptedResidualError mu hmu_nonneg hmu_sum := by
  rw [p11AcceptedOutput_sub_ideal_eq_normalizedResidual mu hmu_nonneg hmu_sum heps]
  have hmass := p11AcceptedResidualDecodedDifference_traceNorm_le_two_mul_mass
    mu hmu_nonneg
  have hsuccess : 0 < kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum :=
    kt19Success_pos_of_errorRate_lt_one p11CubicRowFamily mu hmu_nonneg hmu_sum heps
  simpa [p11AcceptedResidualError] using
    (FiniteDecodedTrace.normalized_residual_traceNorm_le
      (kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum)
      (p11AcceptedResidualMass mu)
      (p11AcceptedResidualDecodedDifference mu) hsuccess hmass)
end QEC.Distillation.KT19Protocol

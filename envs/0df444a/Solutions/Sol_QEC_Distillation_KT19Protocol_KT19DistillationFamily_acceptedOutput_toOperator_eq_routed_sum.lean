-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedOutput_toOperator_eq_routed_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:45:08.367666+00:00
-- url     : https://prove2.me/submissions/67ca1dea-6667-4087-a011-c03bdb04f6a6

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19AcceptedEndpointWeight_pos_of_errorRate_lt_one
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cosetKet_apply
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cosetLabel_eq_combinedWord
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
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
private theorem kt19AcceptedWord_registerPairing_cosetLabel
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (logical : PrimeQuditRegisterLabel q Logical)
    (stabilizer : PrimeQuditRegisterLabel q Stabilizer)
    (haccepted : kt19AcceptedWord R error) :
    registerPairing q error (R.cosetLabel logical stabilizer) =
      registerPairing q (kt19LogicalRouting R error) logical := by
  have hstabilizer :
      wordPairing error (R.stabilizerWord stabilizer) = 0 := by
    unfold CubicRowFamily.stabilizerWord
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro index _
    rw [map_smul]
    have hrow := congrFun haccepted index
    change wordPairing error (R.stabilizerRow index) = 0 at hrow
    rw [hrow, smul_zero]
  change wordPairing error (R.cosetLabel logical stabilizer) =
    wordPairing (kt19LogicalRouting R error) logical
  unfold CubicRowFamily.cosetLabel
  rw [(wordPairing error).map_add, (wordPairing error).map_neg,
    hstabilizer, add_zero]
  unfold CubicRowFamily.logicalWord kt19LogicalRouting
  rw [map_sum]
  simp only [map_smul, wordPairing_apply, dotProduct, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro port _
  ring
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
private theorem kt19Encoding_characterKet_routed_apply
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error)
    (word : PrimeQuditRegisterLabel q Site) :
    R.encodingLinearMap (characterKet q (kt19LogicalRouting R error)) word =
      if word ∈ rowCarrier R then
        CubicRowFamily.cosetNormalization q Stabilizer *
          ((Real.sqrt (q : Real) : Complex)⁻¹ ^ Fintype.card Logical) *
            phase q (registerPairing q error word)
      else 0 := by
  classical
  by_cases hword : word ∈ rowCarrier R
  · obtain ⟨logical, stabilizer, hlabel⟩ :=
      (kt19RowCarrier_mem_iff_exists_cosetLabel R word).mp hword
    rw [if_pos hword]
    change (∑ logical : Logical → ZMod q,
      characterKet q (kt19LogicalRouting R error) logical •
        R.cosetKet logical).ofLp word = _
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [Finset.sum_eq_single logical]
    · have hpairing := kt19AcceptedWord_registerPairing_cosetLabel
        R error logical stabilizer haccepted
      rw [← hlabel, kt19CosetKet_apply_of_cosetLabel R logical stabilizer,
        characterKet_apply, ← hpairing]
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
      characterKet q (kt19LogicalRouting R error) logical •
        R.cosetKet logical).ofLp word = 0
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
private theorem kt19DecoderEncodingIsometry_magicRegisterKet
    (R : CubicRowFamily q Logical Stabilizer Site)
    (label : PrimeQuditRegisterLabel q Logical) :
    kt19DecoderEncodingIsometry R (magicRegisterKet q label) =
      physicalU13 q (R.encodingLinearMap (characterKet q label)) := by
  change physicalU13 q
      (R.encodingLinearMap ((physicalU13 q).symm (magicRegisterKet q label))) = _
  rw [inverseTransversal_magicRegisterKet]
private theorem kt19AcceptedWord_sector_is_routed_encoded
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error) :
    ∃ scale : Complex,
      physicalU13 q (zSyndromeProjector R 0 (characterKet q error)) =
        scale • kt19DecoderEncodingIsometry R
          (magicRegisterKet q (kt19LogicalRouting R error)) := by
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
      zSyndromeProjector R 0 (characterKet q error) =
        scale • R.encodingLinearMap
          (characterKet q (kt19LogicalRouting R error)) := by
    ext word
    change (zSyndromeProjector R 0 (characterKet q error)).ofLp word =
      (scale • R.encodingLinearMap
        (characterKet q (kt19LogicalRouting R error))).ofLp word
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hword : word ∈ rowCarrier R
    · have hsector : zSyndrome R word = 0 :=
        (zSyndrome_eq_zero_iff_mem_rowCarrier R word).mpr hword
      rw [zSyndromeProjector_apply, if_pos hsector,
        kt19Encoding_characterKet_routed_apply R error haccepted word,
        if_pos hword, characterKet_apply]
      change physicalAmplitude * phase q (registerPairing q error word) =
        scale * (encodedAmplitude * phase q (registerPairing q error word))
      rw [← mul_assoc, hscale_encoded]
    · have hsector : zSyndrome R word ≠ 0 := by
        intro hzero
        exact hword ((zSyndrome_eq_zero_iff_mem_rowCarrier R word).mp hzero)
      rw [zSyndromeProjector_apply, if_neg hsector,
        kt19Encoding_characterKet_routed_apply R error haccepted word,
        if_neg hword]
      simp
  refine ⟨scale, ?_⟩
  rw [hprojector, map_smul,
    ← kt19DecoderEncodingIsometry_magicRegisterKet]
private theorem kt19RankOne_smul_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (scalar : Complex) (psi : H) :
    (InnerProductSpace.rankOne Complex (scalar • psi) (scalar • psi)).toLinearMap =
      (star scalar * scalar) •
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  simp [InnerProductSpace.rankOne_apply]
  rw [smul_smul, mul_comm scalar]
private theorem kt19AcceptedWord_accepted_branchOperator_eq_sum
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error) :
    (kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) error).toOperator =
      ∑ _syndrome : ZSyndrome R,
        (InnerProductSpace.rankOne Complex
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))).toLinearMap := by
  classical
  rw [kt19DistillationInstrument,
    FiniteInstrument.binaryCoarsen_branchOperator_accepted,
    Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [Finset.sum_eq_single (0 : Stabilizer → ZMod q)]
  · rw [kt19ProtocolInstrument_branchOperator_wordInputDensity R syndrome 0 error]
    have hsyndrome : xSyndrome R error = 0 := haccepted
    rw [if_pos hsyndrome]
    simp only [kt19Accepts, decide_true, if_true]
    rw [kt19RankOne_smul_self]
    have hphase :
        star (phase q (registerPairing q error
          (zSyndromeRepresentative R syndrome))) *
            phase q (registerPairing q error
              (zSyndromeRepresentative R syndrome)) = 1 := by
      rw [mul_comm]
      exact phase_mul_conj q _
    rw [hphase, one_smul]
  · intro other _ hother
    simp [kt19Accepts, hother]
  · simp
private theorem kt19AcceptedWord_decodedAccepted_eq_routedMagic
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error) :
    kt19DecoderChannel R
      ((kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) error).toOperator) =
      (DensityOperator.pureDensity
        (magicRegisterKet q (kt19LogicalRouting R error)) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num)).toOperator := by
  classical
  let raw : Operator (PrimeQuditRegister q Site) :=
    (kt19DistillationInstrument R).branchOperator .accepted
      (kt19WordInputDensity (Site := Site) error).toOperator
  obtain ⟨scale, hsector⟩ :=
    kt19AcceptedWord_sector_is_routed_encoded R error haccepted
  let coefficient : Complex := ∑ _syndrome : ZSyndrome R, star scale * scale
  have hraw : raw =
      ∑ _syndrome : ZSyndrome R,
        (InnerProductSpace.rankOne Complex
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))).toLinearMap := by
    simpa [raw] using
      kt19AcceptedWord_accepted_branchOperator_eq_sum R error haccepted
  have hdecoded : kt19DecoderChannel R raw =
      coefficient •
        (DensityOperator.pureDensity
          (magicRegisterKet q (kt19LogicalRouting R error)) (by
            rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
              magicRegisterKet_inner_self]
            norm_num)).toOperator := by
    rw [hraw, map_sum]
    simp_rw [hsector, kt19RankOne_smul_self, map_smul,
      kt19DecoderChannel_rankOne_encoded]
    simp only [DensityOperator.pureDensity_toOperator]
    dsimp [coefficient]
    rw [Finset.sum_smul]
  have hraw_trace :
      LinearMap.trace Complex (PrimeQuditRegister q Site) raw = 1 := by
    change LinearMap.trace Complex (PrimeQuditRegister q Site)
      ((kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) error).toOperator) = 1
    rw [(kt19DistillationInstrument R).trace_branchOperator_eq_bornWeight
      .accepted (kt19WordInputDensity (Site := Site) error)]
    have hmass : kt19WordSuccessMass R error = 1 := by
      rw [kt19WordSuccessMass_eq_ite_acceptedWord, if_pos haccepted]
    simpa [kt19WordSuccessMass] using
      congrArg (fun value : Real => (value : Complex)) hmass
  have hdecoded_trace :
      LinearMap.trace Complex (PrimeQuditRegister q Logical)
        (kt19DecoderChannel R raw) = 1 := by
    rw [(kt19DecoderChannel R).trace_map]
    exact hraw_trace
  have hcoefficient : coefficient = 1 := by
    rw [hdecoded, map_smul, DensityOperator.pureDensity_toOperator,
      InnerProductSpace.trace_rankOne, magicRegisterKet_inner_self] at hdecoded_trace
    simpa using hdecoded_trace
  change kt19DecoderChannel R raw = _
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
private theorem kt19DecodedRawAcceptedEndpoint_eq_routedMagic_sum
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    kt19DecoderChannel R (kt19RawEndpoint R mu hmu_nonneg hmu_sum .accepted) =
      ∑ error : PrimeQuditRegisterLabel q Site,
        if kt19AcceptedWord R error then
          (wordProbability q mu error : Complex) •
            (DensityOperator.pureDensity
              (magicRegisterKet q (kt19LogicalRouting R error)) (by
                rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
                  magicRegisterKet_inner_self]
                norm_num)).toOperator
        else 0 := by
  rw [kt19DecodedRawAcceptedEndpoint_eq_acceptedWord_sum
    R mu hmu_nonneg hmu_sum]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccepted : kt19AcceptedWord R error
  · rw [if_pos haccepted, kt19AcceptedDecodedBranch_of_accepted R error haccepted,
      kt19AcceptedWord_decodedAccepted_eq_routedMagic R error haccepted]
    simp [haccepted]
  · simp [haccepted]
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
open QEC.Distillation.KT19Protocol.KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
namespace QEC.Distillation.KT19Protocol.KT19DistillationFamily
theorem _root_.solution
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    (run family mu hmu_nonneg hmu_sum).acceptedOutput.toOperator =
      (kt19Success family.rowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ •
        ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
          if kt19AcceptedWord family.rowFamily error then
            (wordProbability p mu error : Complex) •
              (DensityOperator.pureDensity
                (magicRegisterKet p (kt19Routing family error)) (by
                  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
                    magicRegisterKet_inner_self]
                  norm_num)).toOperator
          else 0 := by
  have hsuccess :
      0 < kt19EndpointWeight family.rowFamily mu hmu_nonneg hmu_sum .accepted :=
    kt19AcceptedEndpointWeight_pos_of_errorRate_lt_one
      family.rowFamily mu hmu_nonneg hmu_sum heps
  change (kt19Run family.rowFamily mu hmu_nonneg hmu_sum).acceptedOutput.toOperator = _
  rw [kt19Run_acceptedOutput,
    kt19EndpointCompletion_eq_conditional_of_pos
      family.rowFamily mu hmu_nonneg hmu_sum .accepted hsuccess]
  dsimp only [kt19EndpointWeight] at hsuccess
  unfold kt19EndpointConditional
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteInstrument.conditionalDensity_toOperator, map_smul]
  change (kt19Success family.rowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ •
      kt19DecoderChannel family.rowFamily
        (kt19RawEndpoint family.rowFamily mu hmu_nonneg hmu_sum .accepted) = _
  rw [kt19DecodedRawAcceptedEndpoint_eq_routedMagic_sum
    family.rowFamily mu hmu_nonneg hmu_sum]
  rfl
end QEC.Distillation.KT19Protocol.KT19DistillationFamily

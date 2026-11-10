-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.kt19AcceptedWord_iff_mem_stabilizerCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:29:13.703677+00:00
-- url     : https://prove2.me/submissions/59447f59-2d47-44c3-af78-dc3b393ca880

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
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
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
namespace QEC.Distillation.KT19Protocol
theorem _root_.solution
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) :
    kt19AcceptedWord R word ↔ word ∈ (kt19StabilizerCode R).dual.carrier := by
  unfold kt19AcceptedWord
  rw [LinearCode.mem_dual]
  change xSyndrome R word = 0 ↔
    ∀ carrier : PrimeQuditRegisterLabel q Site,
      carrier ∈ stabilizerCarrier R → wordPairing word carrier = 0
  constructor
  · intro h carrier hcarrier
    change carrier ∈ Submodule.span (ZMod q) (Set.range R.stabilizerRow) at hcarrier
    induction hcarrier using Submodule.span_induction with
    | mem carrier hcarrier =>
        rcases hcarrier with ⟨index, rfl⟩
        simpa [xSyndrome] using congrFun h index
    | zero => simp
    | add left right _ _ hleft hright =>
        rw [(wordPairing word).map_add, hleft, hright, add_zero]
    | smul scalar carrier _ hcarrier =>
        rw [(wordPairing word).map_smul, hcarrier, smul_zero]
  · intro h
    funext index
    have hrow : R.stabilizerRow index ∈ stabilizerCarrier R := by
      unfold stabilizerCarrier
      exact Submodule.subset_span ⟨index, rfl⟩
    simpa [xSyndrome] using h (R.stabilizerRow index) hrow
end QEC.Distillation.KT19Protocol

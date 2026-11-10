-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.p11OutputWorstPortError_le_two_mul_card_mul_residualError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:47:41.321477+00:00
-- url     : https://prove2.me/submissions/2b7fc400-11ac-4198-a967-a69ce94460b7

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_p11AcceptedOutputTraceNorm_sub_ideal_le_two_mul_residualError
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterKet_inner
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
import Theorems.Thm_QEC_Semantics_norm_trace_le_traceNorm
import Theorems.Thm_QEC_Semantics_operatorNorm_projection_le
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
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
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
private theorem p11OutputLabelDistribution_eq_rankOneTrace
    (rho : DensityOperator (PrimeQuditRegister 11 (Fin 2)))
    (label : PrimeQuditRegisterLabel 11 (Fin 2)) :
    kt19OutputLabelDistribution rho label =
      (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
        ((InnerProductSpace.rankOne Complex (magicRegisterKet 11 label)
          (magicRegisterKet 11 label)).toLinearMap * rho.toOperator)).re := by
  classical
  let P : Operator (PrimeQuditRegister 11 (Fin 2)) :=
    (InnerProductSpace.rankOne Complex (magicRegisterKet 11 label)
      (magicRegisterKet 11 label)).toLinearMap
  have hnorm : ‖magicRegisterKet 11 label‖ = 1 := by
    have hnormSq : ‖magicRegisterKet 11 label‖ ^ 2 = 1 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
        magicRegisterKet_inner_self]
      norm_num
    nlinarith [norm_nonneg (magicRegisterKet 11 label)]
  have hP : P.IsSymmetricProjection := by
    simpa [P] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self
        (𝕜 := Complex) hnorm)
  have hPself : LinearMap.adjoint P = P :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp hP.isSymmetric
  have hPidemp : P * P = P := hP.isIdempotentElem.eq
  unfold kt19OutputLabelDistribution FiniteInstrument.bornWeight
  rw [FiniteInstrument.branchOperator_apply]
  rw [Fintype.sum_eq_single label]
  · simp only [magicRegisterInstrument, magicRegisterKrausFamily, id_eq, ↓reduceIte]
    change Complex.re (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
      (P * (rho.toOperator * LinearMap.adjoint P))) =
        Complex.re (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * rho.toOperator))
    rw [hPself]
    calc
      Complex.re (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * (rho.toOperator * P))) =
          Complex.re (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
            ((P * rho.toOperator) * P)) := by
              congr 2
      _ = Complex.re (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * (P * rho.toOperator))) := by
            rw [LinearMap.trace_mul_comm]
      _ = Complex.re (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * rho.toOperator)) := by
            rw [← mul_assoc, hPidemp]
  · intro other hother
    simp [magicRegisterInstrument, magicRegisterKrausFamily, hother]
private theorem p11Trace_rankOne_mul
    (u : PrimeQuditRegister 11 (Fin 2))
    (A : Operator (PrimeQuditRegister 11 (Fin 2))) :
    LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
      ((InnerProductSpace.rankOne Complex u u).toLinearMap * A) =
        inner Complex u (A u) := by
  rw [LinearMap.trace_mul_comm]
  have hcomp : A * (InnerProductSpace.rankOne Complex u u).toLinearMap =
      (InnerProductSpace.rankOne Complex (A u) u).toLinearMap := by
    ext vector
    simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
      InnerProductSpace.rankOne_apply]
  rw [hcomp]
  exact InnerProductSpace.trace_rankOne (A u) u
private theorem kt19OutputLabelDistribution_le_traceNorm_sub_ideal_of_ne
    (rho : DensityOperator (PrimeQuditRegister 11 (Fin 2)))
    (label : PrimeQuditRegisterLabel 11 (Fin 2)) (hlabel : label ≠ 0) :
    kt19OutputLabelDistribution rho label ≤
      traceNorm (rho.toOperator -
        (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) := by
  classical
  let P : Operator (PrimeQuditRegister 11 (Fin 2)) :=
    (InnerProductSpace.rankOne Complex (magicRegisterKet 11 label)
      (magicRegisterKet 11 label)).toLinearMap
  have hnorm : ‖magicRegisterKet 11 label‖ = 1 := by
    have hnormSq : ‖magicRegisterKet 11 label‖ ^ 2 = 1 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
        magicRegisterKet_inner_self]
      norm_num
    nlinarith [norm_nonneg (magicRegisterKet 11 label)]
  have hP : P.IsSymmetricProjection := by
    simpa [P] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self
        (𝕜 := Complex) hnorm)
  have hprojector : IsStarProjection P := by
    rw [LinearMap.isStarProjection_iff_isSymmetricProjection]
    exact hP
  have hideal :
      (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
        (P * (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator)).re = 0 := by
    dsimp [P]
    rw [kt19IdealOutput, DensityOperator.pureDensity_toOperator,
      p11Trace_rankOne_mul]
    simp [InnerProductSpace.rankOne_apply, magicRegisterKet_inner,
      hlabel, Ne.symm hlabel]
  have hraw :
      kt19OutputLabelDistribution rho label =
        (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * rho.toOperator)).re := by
    simpa [P] using p11OutputLabelDistribution_eq_rankOneTrace rho label
  have hcenter :
      (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
        (P * rho.toOperator)).re =
        (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * (rho.toOperator -
            (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator))).re := by
    rw [mul_sub, map_sub, Complex.sub_re, hideal, sub_zero]
  calc
    kt19OutputLabelDistribution rho label =
        (LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * (rho.toOperator -
            (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator))).re := hraw.trans hcenter
    _ ≤ |(LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * (rho.toOperator -
            (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator))).re| := le_abs_self _
    _ ≤ ‖LinearMap.trace Complex (PrimeQuditRegister 11 (Fin 2))
          (P * (rho.toOperator -
            (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ traceNorm (P * (rho.toOperator -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator)) :=
      norm_trace_le_traceNorm _
    _ ≤ operatorNorm P * traceNorm (rho.toOperator -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) :=
      traceNorm_mul_left_le _ _
    _ ≤ 1 * traceNorm (rho.toOperator -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) := by
      exact mul_le_mul_of_nonneg_right
        (operatorNorm_projection_le P hprojector) (traceNorm_nonneg _)
    _ = traceNorm (rho.toOperator -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) := by ring
private theorem kt19OutputPortError_le_card_mul_traceNorm_sub_ideal
    (rho : DensityOperator (PrimeQuditRegister 11 (Fin 2))) (port : Fin 2) :
    kt19OutputPortError rho port ≤
      (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
        traceNorm (rho.toOperator -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) := by
  classical
  unfold kt19OutputPortError
  calc
    (∑ label : PrimeQuditRegisterLabel 11 (Fin 2),
      if label port = 0 then 0 else kt19OutputLabelDistribution rho label) ≤
        ∑ _label : PrimeQuditRegisterLabel 11 (Fin 2),
          traceNorm (rho.toOperator -
            (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) := by
      apply Finset.sum_le_sum
      intro label _
      by_cases hport : label port = 0
      · simp [hport, traceNorm_nonneg]
      · rw [if_neg hport]
        apply kt19OutputLabelDistribution_le_traceNorm_sub_ideal_of_ne rho label
        intro hzero
        apply hport
        simpa [hzero]
    _ = (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
        traceNorm (rho.toOperator -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) := by
      simp
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
    kt19OutputWorstPortError
      ((kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput) ≤
      2 * (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
        p11AcceptedResidualError mu hmu_nonneg hmu_sum := by
  classical
  unfold kt19OutputWorstPortError
  apply Finset.sup'_le
  intro port _
  calc
    kt19OutputPortError
        ((kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput) port ≤
        (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
          traceNorm
            ((kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput.toOperator -
              (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator) :=
      kt19OutputPortError_le_card_mul_traceNorm_sub_ideal _ port
    _ ≤ (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
          (2 * p11AcceptedResidualError mu hmu_nonneg hmu_sum) :=
      mul_le_mul_of_nonneg_left
        (p11AcceptedOutputTraceNorm_sub_ideal_le_two_mul_residualError
          mu hmu_nonneg hmu_sum heps) (Nat.cast_nonneg _)
    _ = 2 * (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
          p11AcceptedResidualError mu hmu_nonneg hmu_sum := by ring
end QEC.Distillation.KT19Protocol

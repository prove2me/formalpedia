-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.outputLabelDistribution_eq_routedMass_div_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:47:43.828766+00:00
-- url     : https://prove2.me/submissions/fdc64a96-58a5-4154-b461-e93511ccd9c5

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_acceptedOutput_toOperator_eq_routed_sum
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
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
omit [Fact p.Prime] in
/-- One complete generic-family magic-register readout weight is the trace
of its actual rank-one label projector. -/
private theorem outputLabelDistribution_eq_rankOneTrace
    (rho : DensityOperator (PrimeQuditRegister p (Fin k)))
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    kt19OutputLabelDistribution rho label =
      (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
        ((InnerProductSpace.rankOne Complex (magicRegisterKet p label)
          (magicRegisterKet p label)).toLinearMap * rho.toOperator)).re := by
  classical
  let P : Operator (PrimeQuditRegister p (Fin k)) :=
    (InnerProductSpace.rankOne Complex (magicRegisterKet p label)
      (magicRegisterKet p label)).toLinearMap
  have hnorm : ‖magicRegisterKet p label‖ = 1 := by
    have hnormSq : ‖magicRegisterKet p label‖ ^ 2 = 1 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
        magicRegisterKet_inner_self]
      norm_num
    nlinarith [norm_nonneg (magicRegisterKet p label)]
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
    change Complex.re (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
      (P * (rho.toOperator * LinearMap.adjoint P))) =
        Complex.re (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
          (P * rho.toOperator))
    rw [hPself]
    calc
      Complex.re (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
          (P * (rho.toOperator * P))) =
          Complex.re (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
            ((P * rho.toOperator) * P)) := by
              congr 2
      _ = Complex.re (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
          (P * (P * rho.toOperator))) := by
            rw [LinearMap.trace_mul_comm]
      _ = Complex.re (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
          (P * rho.toOperator)) := by
            rw [← mul_assoc, hPidemp]
  · intro other hother
    simp [magicRegisterInstrument, magicRegisterKrausFamily, hother]
omit [Fact p.Prime] in
/-- The trace of a rank-one left projector against an operator is its
corresponding quadratic form. -/
private theorem trace_rankOne_mul
    (u : PrimeQuditRegister p (Fin k))
    (A : Operator (PrimeQuditRegister p (Fin k))) :
    LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
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
private theorem trace_magicProjector_mul_pureMagic
    (observed routed : PrimeQuditRegisterLabel p (Fin k)) :
    LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
      ((InnerProductSpace.rankOne Complex (magicRegisterKet p observed)
          (magicRegisterKet p observed)).toLinearMap *
        (DensityOperator.pureDensity (magicRegisterKet p routed) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num)).toOperator) =
      if observed = routed then 1 else 0 := by
  rw [DensityOperator.pureDensity_toOperator, trace_rankOne_mul]
  by_cases hroute : observed = routed
  · subst routed
    have hnorm : ‖magicRegisterKet p observed‖ = 1 := by
      have hnormSq : ‖magicRegisterKet p observed‖ ^ 2 = 1 := by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
          magicRegisterKet_inner_self]
        norm_num
      nlinarith [norm_nonneg (magicRegisterKet p observed)]
    simp [InnerProductSpace.rankOne_apply, hnorm]
  · have hroute' : routed ≠ observed := Ne.symm hroute
    simp [hroute, hroute', InnerProductSpace.rankOne_apply,
      magicRegisterKet_inner]
private theorem trace_magicProjector_mul_routed_sum
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (label : PrimeQuditRegisterLabel p (Fin k)) :
    LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
      ((InnerProductSpace.rankOne Complex (magicRegisterKet p label)
          (magicRegisterKet p label)).toLinearMap *
        (∑ error : Word (ZMod p) (KeptPunctureLocation p k),
          if kt19AcceptedWord family.rowFamily error then
            (wordProbability p mu error : Complex) •
              (DensityOperator.pureDensity
                (magicRegisterKet p (kt19Routing family error)) (by
                  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
                    magicRegisterKet_inner_self]
                  norm_num)).toOperator
          else 0)) =
      (routedAcceptedMass family mu label : Complex) := by
  classical
  rw [Finset.mul_sum, map_sum, routedAcceptedMass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccepted : kt19AcceptedWord family.rowFamily error
  · by_cases hrouted : label = kt19Routing family error
    · simp only [haccepted, hrouted, and_self, if_true]
      rw [Algebra.mul_smul_comm, map_smul,
        trace_magicProjector_mul_pureMagic]
      simp
    · simp only [haccepted, true_and, if_true, hrouted, if_false]
      rw [Algebra.mul_smul_comm, map_smul,
        trace_magicProjector_mul_pureMagic]
      simp [hrouted]
  · simp [haccepted]
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
    (heps : kt19ErrorRate mu < 1)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    kt19OutputLabelDistribution
        (run family mu hmu_nonneg hmu_sum).acceptedOutput label =
      routedAcceptedMass family mu label /
        kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
  classical
  let P : Operator (PrimeQuditRegister p (Fin k)) :=
    (InnerProductSpace.rankOne Complex (magicRegisterKet p label)
      (magicRegisterKet p label)).toLinearMap
  have htrace :
      LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
        (P * (run family mu hmu_nonneg hmu_sum).acceptedOutput.toOperator) =
          ((routedAcceptedMass family mu label /
            kt19Success family.rowFamily mu hmu_nonneg hmu_sum : Real) : Complex) := by
    rw [acceptedOutput_toOperator_eq_routed_sum
      family mu hmu_nonneg hmu_sum heps]
    rw [Algebra.mul_smul_comm, map_smul]
    change (kt19Success family.rowFamily mu hmu_nonneg hmu_sum : Complex)⁻¹ *
        LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
          ((InnerProductSpace.rankOne Complex (magicRegisterKet p label)
              (magicRegisterKet p label)).toLinearMap *
            (∑ error : Word (ZMod p) (KeptPunctureLocation p k),
              if kt19AcceptedWord family.rowFamily error then
                (wordProbability p mu error : Complex) •
                  (DensityOperator.pureDensity
                    (magicRegisterKet p (kt19Routing family error)) (by
                      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
                        magicRegisterKet_inner_self]
                      norm_num)).toOperator
              else 0)) = _
    rw [trace_magicProjector_mul_routed_sum]
    rw [Complex.ofReal_div, div_eq_mul_inv]
    ring
  rw [outputLabelDistribution_eq_rankOneTrace]
  change (LinearMap.trace Complex (PrimeQuditRegister p (Fin k))
    (P * (run family mu hmu_nonneg hmu_sum).acceptedOutput.toOperator)).re = _
  rw [htrace]
  simp
end QEC.Distillation.KT19Protocol.KT19DistillationFamily

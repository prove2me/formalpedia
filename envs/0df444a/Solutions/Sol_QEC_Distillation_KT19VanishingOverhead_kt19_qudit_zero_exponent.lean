-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19_qudit_zero_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:38:39.716194+00:00
-- url     : https://prove2.me/submissions/2efd5581-9c0f-41ac-a7f0-d6145ed6df4d

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Definitions.Def_QEC_Results_Distillation_PrimeQuditOverhead
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_kt19_family_parameters
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_physicalGate_implements_inverseLogicalU13
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19ChangingPrimeExponent
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrime
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
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply
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


section
noncomputable section
namespace QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
section PrimeQuditOverheadPrivateHelpers
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
private theorem primeQuditOverhead_kt19FixedPrimeLogGrowthBase_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : primeQuditOverhead_kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    0 < primeQuditOverhead_kt19FixedPrimeLogGrowthBase family mu := by
  unfold primeQuditOverhead_kt19FixedPrimeLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (primeQuditOverhead_kt19FixedPrimeIterationScale_pos family) hepsilon
  · exact hsmall.trans_lt (by norm_num)
private theorem primeQuditOverhead_kt19FixedPrimeCostCoefficient_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : primeQuditOverhead_kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    0 < kt19FixedPrimeCostCoefficient family mu := by
  unfold kt19FixedPrimeCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (primeQuditOverhead_kt19FixedPrimeLogGrowthBase_pos family mu hmu_nonneg hmu_sum
        hepsilon hsmall) _)
private theorem primeQuditOverhead_kt19SmallIIDLaw_errorRate
    (family : KT19DistillationFamily p l k) :
    kt19ErrorRate (primeQuditOverhead_kt19SmallIIDLaw family) = primeQuditOverhead_kt19SmallIIDRate family := by
  simp [kt19ErrorRate, primeQuditOverhead_kt19SmallIIDLaw]
private theorem primeQuditOverhead_kt19SmallIIDLaw_scaled_small
    (family : KT19DistillationFamily p l k) :
    primeQuditOverhead_kt19FixedPrimeIterationScale family *
        kt19ErrorRate (primeQuditOverhead_kt19SmallIIDLaw family) ≤ 1 / 4 := by
  rw [primeQuditOverhead_kt19SmallIIDLaw_errorRate]
  unfold primeQuditOverhead_kt19SmallIIDRate
  have hscale_ne : primeQuditOverhead_kt19FixedPrimeIterationScale family ≠ 0 :=
    (primeQuditOverhead_kt19FixedPrimeIterationScale_pos family).ne'
  have hproduct :
      primeQuditOverhead_kt19FixedPrimeIterationScale family *
          (1 / (4 * primeQuditOverhead_kt19FixedPrimeIterationScale family)) = (1 / 4 : ℝ) := by
    field_simp [hscale_ne]
  rw [hproduct]
private theorem primeQuditOverhead_kt19FixedFamilyPhysicalPackage
    (family : KT19DistillationFamily p l k) (hdistance : 2 ≤ l - k) :
    let mu := primeQuditOverhead_kt19SmallIIDLaw family
    let hmu_nonneg := primeQuditOverhead_kt19SmallIIDLaw_nonneg family
    let hmu_sum := primeQuditOverhead_kt19SmallIIDLaw_sum family
    ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
      ∃ gate : UnitaryTransport
          (PrimeQuditRegister p (KeptPunctureLocation p k))
          (PrimeQuditRegister p (KeptPunctureLocation p k)),
        ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
            (PrimeQuditRegister p (KeptPunctureLocation p k))
            (PrimeQuditRegister p (Fin k)),
          resource = family.inputResource mu hmu_nonneg hmu_sum ∧
            gate = family.physicalGate ∧
              protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                  Admissible p l k ∧
                    2 ≤ l - k ∧
                      kt19Length p k = p - k ∧
                        kt19LogicalDimension p l k = k ∧
                          kt19SafeDistance p l k ≥ l - k ∧
                            stabilizerCarrier family.rowFamily =
                              (shortenedReedSolomonCode p l k).carrier ∧
                              family.encodedCode.ImplementsLogicalGate gate
                                family.rowFamily.logicalInverseU13 ∧
                                0 < kt19ErrorRate mu ∧
                                  ∃ coefficient : ℝ,
                                    0 < coefficient ∧
                                      coefficient = kt19FixedPrimeCostCoefficient family mu ∧
                                      kt19FixedPrimeGamma p l k =
                                        Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                          Real.log ((l - k : Nat) : ℝ) ∧
                                      Tendsto (fun depth : Nat =>
                                        kt19FixedPrimeScheduleTargetError family mu depth)
                                        atTop (𝓝 0) ∧
                                      Tendsto (fun depth : Nat =>
                                        kt19FixedPrimeActualOutputError family mu
                                          hmu_nonneg hmu_sum depth)
                                        atTop (𝓝 0) ∧
                                      DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                        (fun depth => kt19FixedPrimeInputSlots p k depth)
                                        (fun depth => kt19FixedPrimeOutputSlots k depth)
                                        (kt19FixedPrimeScheduleTargetError family mu)
                                        (kt19FixedPrimeActualOutputError family mu
                                          hmu_nonneg hmu_sum)
                                        (kt19FixedPrimeExpectedYield family mu
                                          hmu_nonneg hmu_sum)
                                        (kt19FixedPrimeGamma p l k) coefficient := by
  let mu : ZMod p → ℝ := primeQuditOverhead_kt19SmallIIDLaw family
  have hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a :=
    primeQuditOverhead_kt19SmallIIDLaw_nonneg family
  have hmu_sum : ∑ a : ZMod p, mu a = 1 :=
    primeQuditOverhead_kt19SmallIIDLaw_sum family
  have hepsilon : 0 < kt19ErrorRate mu := by
    rw [primeQuditOverhead_kt19SmallIIDLaw_errorRate]
    exact primeQuditOverhead_kt19SmallIIDRate_pos family
  have hsmall :
      primeQuditOverhead_kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4 :=
    primeQuditOverhead_kt19SmallIIDLaw_scaled_small family
  have hfixed := kt19FixedPrime family mu hmu_nonneg hmu_sum hdistance hepsilon hsmall
  have hparameters := kt19_family_parameters p l k family.admissible
  have hcoefficient : 0 < kt19FixedPrimeCostCoefficient family mu :=
    primeQuditOverhead_kt19FixedPrimeCostCoefficient_pos family mu hmu_nonneg hmu_sum hepsilon hsmall
  change ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
    ∃ gate : UnitaryTransport
        (PrimeQuditRegister p (KeptPunctureLocation p k))
        (PrimeQuditRegister p (KeptPunctureLocation p k)),
      ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
          (PrimeQuditRegister p (KeptPunctureLocation p k))
          (PrimeQuditRegister p (Fin k)),
        resource = family.inputResource mu hmu_nonneg hmu_sum ∧
          gate = family.physicalGate ∧
            protocol = family.protocol mu hmu_nonneg hmu_sum ∧
              protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                Admissible p l k ∧
                  2 ≤ l - k ∧
                    kt19Length p k = p - k ∧
                      kt19LogicalDimension p l k = k ∧
                        kt19SafeDistance p l k ≥ l - k ∧
                          stabilizerCarrier family.rowFamily =
                            (shortenedReedSolomonCode p l k).carrier ∧
                            family.encodedCode.ImplementsLogicalGate gate
                              family.rowFamily.logicalInverseU13 ∧
                              0 < kt19ErrorRate mu ∧
                                ∃ coefficient : ℝ,
                                  0 < coefficient ∧
                                    coefficient = kt19FixedPrimeCostCoefficient family mu ∧
                                    kt19FixedPrimeGamma p l k =
                                      Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                        Real.log ((l - k : Nat) : ℝ) ∧
                                    Tendsto (fun depth : Nat =>
                                      kt19FixedPrimeScheduleTargetError family mu depth)
                                      atTop (𝓝 0) ∧
                                    Tendsto (fun depth : Nat =>
                                      kt19FixedPrimeActualOutputError family mu
                                        hmu_nonneg hmu_sum depth) atTop (𝓝 0) ∧
                                    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                      (fun depth => kt19FixedPrimeInputSlots p k depth)
                                      (fun depth => kt19FixedPrimeOutputSlots k depth)
                                      (kt19FixedPrimeScheduleTargetError family mu)
                                      (kt19FixedPrimeActualOutputError family mu
                                        hmu_nonneg hmu_sum)
                                      (kt19FixedPrimeExpectedYield family mu
                                        hmu_nonneg hmu_sum)
                                      (kt19FixedPrimeGamma p l k) coefficient
  refine ⟨family.inputResource mu hmu_nonneg hmu_sum, family.physicalGate,
    family.protocol mu hmu_nonneg hmu_sum, rfl, rfl, rfl, rfl,
    family.admissible, hdistance, hparameters.1, hparameters.2.1,
    hparameters.2.2, family.stabilizerCarrier_eq_shortened,
    KT19DistillationFamily.physicalGate_implements_inverseLogicalU13 family, hepsilon,
    kt19FixedPrimeCostCoefficient family mu, hcoefficient, rfl, rfl, hfixed.1,
    hfixed.2.1, ?_⟩
  simpa using hfixed.2.2
end PrimeQuditOverheadPrivateHelpers
end QEC.Distillation.KT19VanishingOverhead
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19VanishingOverhead
theorem _root_.solution :
    (∀ (p l k : Nat) (hp : Nat.Prime p) (hfive : 5 ≤ p)
        (hadmissible : Admissible p l k) (hdistance : 2 ≤ l - k),
      letI : NeZero p := ⟨hp.ne_zero⟩
      letI : Fact p.Prime := ⟨hp⟩
      ∃ family : KT19DistillationFamily p l k,
        family = kt19ExplicitFixedPrimeDistillationFamily p l k hfive hadmissible ∧
          let mu := primeQuditOverhead_kt19SmallIIDLaw family
          let hmu_nonneg := primeQuditOverhead_kt19SmallIIDLaw_nonneg family
          let hmu_sum := primeQuditOverhead_kt19SmallIIDLaw_sum family
          ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
            ∃ gate : UnitaryTransport
                (PrimeQuditRegister p (KeptPunctureLocation p k))
                (PrimeQuditRegister p (KeptPunctureLocation p k)),
              ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
                  (PrimeQuditRegister p (KeptPunctureLocation p k))
                  (PrimeQuditRegister p (Fin k)),
                resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                  gate = family.physicalGate ∧
                    protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                      protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                        Admissible p l k ∧
                          2 ≤ l - k ∧
                            kt19Length p k = p - k ∧
                              kt19LogicalDimension p l k = k ∧
                                kt19SafeDistance p l k ≥ l - k ∧
                                  stabilizerCarrier family.rowFamily =
                                    (shortenedReedSolomonCode p l k).carrier ∧
                                    family.encodedCode.ImplementsLogicalGate gate
                                      family.rowFamily.logicalInverseU13 ∧
                                      0 < kt19ErrorRate mu ∧
                                        ∃ coefficient : ℝ,
                                          0 < coefficient ∧
                                            coefficient =
                                              kt19FixedPrimeCostCoefficient family mu ∧
                                            kt19FixedPrimeGamma p l k =
                                              Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                                Real.log ((l - k : Nat) : ℝ) ∧
                                            Tendsto (fun depth : Nat =>
                                              kt19FixedPrimeScheduleTargetError family mu depth)
                                              atTop (𝓝 0) ∧
                                            Tendsto (fun depth : Nat =>
                                              kt19FixedPrimeActualOutputError family mu
                                                hmu_nonneg hmu_sum depth)
                                              atTop (𝓝 0) ∧
                                            DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                              (fun depth => kt19FixedPrimeInputSlots p k depth)
                                              (fun depth => kt19FixedPrimeOutputSlots k depth)
                                              (kt19FixedPrimeScheduleTargetError family mu)
                                              (kt19FixedPrimeActualOutputError family mu
                                                hmu_nonneg hmu_sum)
                                              (kt19FixedPrimeExpectedYield family mu
                                                hmu_nonneg hmu_sum)
                                              (kt19FixedPrimeGamma p l k) coefficient) ∧
      ∀ (bound : Nat) (eta : ℝ), 0 < eta →
        ∃ p : Nat, ∃ hp : Nat.Prime p, ∃ hlarge : 32 ≤ p,
          bound ≤ p ∧ p ≡ 1 [MOD 8] ∧
            letI : NeZero p := ⟨hp.ne_zero⟩
            letI : Fact p.Prime := ⟨hp⟩
            ∃ family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p),
              family = kt19ExplicitDistillationFamily p hlarge ∧
                kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta ∧
                let mu := primeQuditOverhead_kt19SmallIIDLaw family
                let hmu_nonneg := primeQuditOverhead_kt19SmallIIDLaw_nonneg family
                let hmu_sum := primeQuditOverhead_kt19SmallIIDLaw_sum family
                ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
                  ∃ gate : UnitaryTransport
                      (PrimeQuditRegister p
                        (KeptPunctureLocation p (kt19ExplicitK p)))
                      (PrimeQuditRegister p
                        (KeptPunctureLocation p (kt19ExplicitK p))),
                    ∃ protocol : MagicStateDistillationProtocol
                        (KT19SingleQudit.{0} p)
                        (PrimeQuditRegister p
                          (KeptPunctureLocation p (kt19ExplicitK p)))
                        (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
                      resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                        gate = family.physicalGate ∧
                          protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                            protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                              Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                                stabilizerCarrier family.rowFamily =
                                  (shortenedReedSolomonCode p (kt19ExplicitL p)
                                    (kt19ExplicitK p)).carrier ∧
                                  family.encodedCode.ImplementsLogicalGate gate
                                    family.rowFamily.logicalInverseU13 := by
  constructor
  · intro p l k hp hfive hadmissible hdistance
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    let family : KT19DistillationFamily p l k :=
      kt19ExplicitFixedPrimeDistillationFamily p l k hfive hadmissible
    refine ⟨family, rfl, ?_⟩
    exact primeQuditOverhead_kt19FixedFamilyPhysicalPackage family hdistance
  · intro bound eta heta
    rcases kt19ChangingPrimeExponent bound eta heta with
      ⟨p, hbound, hp, hlarge, hmod, hgamma⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    let family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p) :=
      kt19ExplicitDistillationFamily p hlarge
    let mu : ZMod p → ℝ := primeQuditOverhead_kt19SmallIIDLaw family
    have hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a :=
      primeQuditOverhead_kt19SmallIIDLaw_nonneg family
    have hmu_sum : ∑ a : ZMod p, mu a = 1 :=
      primeQuditOverhead_kt19SmallIIDLaw_sum family
    refine ⟨p, hp, hlarge, hbound, hmod, ?_⟩
    change ∃ family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p),
      family = kt19ExplicitDistillationFamily p hlarge ∧
        kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta ∧
        let mu := primeQuditOverhead_kt19SmallIIDLaw family
        let hmu_nonneg := primeQuditOverhead_kt19SmallIIDLaw_nonneg family
        let hmu_sum := primeQuditOverhead_kt19SmallIIDLaw_sum family
        ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
          ∃ gate : UnitaryTransport
              (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
              (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p))),
            ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
                (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
                (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
              resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                gate = family.physicalGate ∧
                  protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                    protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                      Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                        stabilizerCarrier family.rowFamily =
                          (shortenedReedSolomonCode p (kt19ExplicitL p)
                            (kt19ExplicitK p)).carrier ∧
                          family.encodedCode.ImplementsLogicalGate gate
                            family.rowFamily.logicalInverseU13
    refine ⟨family, rfl, hgamma, ?_⟩
    change ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
      ∃ gate : UnitaryTransport
          (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
          (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p))),
        ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
            (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
            (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
          resource = family.inputResource mu hmu_nonneg hmu_sum ∧
            gate = family.physicalGate ∧
              protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                  Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                    stabilizerCarrier family.rowFamily =
                      (shortenedReedSolomonCode p (kt19ExplicitL p)
                        (kt19ExplicitK p)).carrier ∧
                      family.encodedCode.ImplementsLogicalGate gate
                        family.rowFamily.logicalInverseU13
    refine ⟨family.inputResource mu hmu_nonneg hmu_sum, family.physicalGate,
      family.protocol mu hmu_nonneg hmu_sum, rfl, rfl, rfl, rfl,
      family.admissible, family.stabilizerCarrier_eq_shortened,
      KT19DistillationFamily.physicalGate_implements_inverseLogicalU13 family⟩
end QEC.Distillation.KT19VanishingOverhead

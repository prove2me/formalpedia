-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19SelectedPortDensity_eq_singleSiteResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:23:11.470136+00:00
-- url     : https://prove2.me/submissions/84211a13-2af5-484b-bde1-bc2367f3f2e9

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19SelectedPortDensity_eq_actualMarginal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_acceptedOutput_toOperator_eq_routed_sum
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_outputLabelDistribution_eq_routedMass_div_success
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_recombine_splitLabel
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
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
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
universe u
private theorem kt19RegisterPairing_split_port (p k : Nat) [NeZero p]
    (port : Fin k) (e x : PrimeQuditRegisterLabel p (Fin k)) :
    registerPairing p e x = e port * x port +
      ∑ site : {site : Fin k // site ≠ port}, e site * x site := by
  unfold registerPairing
  rw [Fintype.sum_eq_add_sum_subtype_ne _ port]
private theorem kt19CubicExponent_split_port (p k : Nat) [NeZero p]
    (port : Fin k) (x : PrimeQuditRegisterLabel p (Fin k)) :
    cubicExponent p x = x port ^ 3 +
      ∑ site : {site : Fin k // site ≠ port}, x site ^ 3 := by
  unfold cubicExponent
  rw [Fintype.sum_eq_add_sum_subtype_ne _ port]
private theorem kt19PrimeQuditRegisterQuditTransport_apply
    (p : Nat) [NeZero p] (Site : Type u) [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : Qudit.Label (fun _ : Site => p)) :
    kt19PrimeQuditRegisterQuditTransport p Site psi label =
      psi ((kt19PrimeQuditLabelEquiv p Site).symm label) := by
  have hinner := (kt19PrimeQuditRegisterQuditTransport p Site).map_inner
    (EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex
      ((kt19PrimeQuditLabelEquiv p Site).symm label)) psi
  rw [kt19PrimeQuditRegisterQuditTransport_apply_basis,
    (kt19PrimeQuditLabelEquiv p Site).apply_symm_apply,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner] at hinner
  exact hinner
private theorem kt19SelectedPortTransport_symm_apply (p k : Nat) [NeZero p]
    (port : Fin k) (psi : KT19SingleQudit.{0} p)
    (label : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) :
    (kt19SelectedPortTransport p k port).symm psi label =
      psi (kt19SelectedPortLabelEquiv p k port label) := by
  have hinner := (kt19SelectedPortTransport p k port).map_inner
    (EuclideanSpace.basisFun
      (Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) Complex label)
    ((kt19SelectedPortTransport p k port).symm psi)
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [kt19SelectedPortTransport_apply_basis, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
private theorem kt19SelectedPortRegisterFactorization_symm_tmul_apply
    (p k : Nat) [NeZero p] (port : Fin k)
    (leftState : (kt19SelectedPortSubsystem p k port).selectedSystem)
    (rightState : (kt19SelectedPortSubsystem p k port).complementSystem)
    (labels : Qudit.Label (fun _ : Fin k => p)) :
    (kt19SelectedPortSubsystem p k port).registerFactorization.symm
        (leftState ⊗ₜ[Complex] rightState) labels =
      leftState ((kt19SelectedPortSubsystem p k port).splitLabel labels).1 *
        rightState ((kt19SelectedPortSubsystem p k port).splitLabel labels).2 := by
  have hinner := (kt19SelectedPortSubsystem p k port).registerFactorization.map_inner
    (EuclideanSpace.basisFun _ Complex labels)
    ((kt19SelectedPortSubsystem p k port).registerFactorization.symm
      (leftState ⊗ₜ[Complex] rightState))
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [QuditSubsystem.registerFactorization_apply_basis, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
private theorem kt19PrimeQuditLabelEquiv_symm_recombine_apply_port
    (p k : Nat) [NeZero p] (port : Fin k)
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    (kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)) port =
      ZMod.finEquiv p (left (kt19SelectedPortCoordinate p k port)) := by
  simp [kt19PrimeQuditLabelEquiv, QuditSubsystem.recombineLabel,
    kt19SelectedPortSubsystem, kt19SelectedPortCoordinate]
private theorem kt19PrimeQuditLabelEquiv_symm_recombine_apply_ne
    (p k : Nat) [NeZero p] (port : Fin k)
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions)
    (site : {site : Fin k // site ≠ port}) :
    (kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)) site =
      ZMod.finEquiv p (right ⟨site, by simpa [kt19SelectedPortSubsystem] using site.property⟩) := by
  simp [kt19PrimeQuditLabelEquiv, QuditSubsystem.recombineLabel,
    kt19SelectedPortSubsystem, site.property]
private theorem kt19PrimeQuditLabelEquiv_symm_recombine_zero_apply_port
    (p k : Nat) [NeZero p] (port : Fin k)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    (kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right)) port = 0 := by
  rw [kt19PrimeQuditLabelEquiv_symm_recombine_apply_port]
  simp [kt19SelectedPortZeroLabel, Qudit.zeroLabel]
private theorem kt19SelectedPortMagicState_zero_ne_zero
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortMagicState p k port label).ofLp
        (kt19SelectedPortZeroLabel p k port) ≠ 0 := by
  rw [kt19SelectedPortMagicState, kt19SelectedPortTransport_symm_apply,
    magicRegisterKet_apply]
  apply mul_ne_zero
  · apply pow_ne_zero
    apply inv_ne_zero
    have hpos : (0 : Real) < (p : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hpos)
  · intro hphase
    have hunit := phase_mul_conj p
      (registerPairing p (kt19SingleSiteLabel (label port))
        (kt19SelectedPortLabelEquiv p k port (kt19SelectedPortZeroLabel p k port)) +
          cubicExponent p (kt19SelectedPortLabelEquiv p k port
            (kt19SelectedPortZeroLabel p k port)))
    rw [hphase, zero_mul] at hunit
    norm_num at hunit
private theorem kt19SelectedPortLabelEquiv_eq_singleSiteLabel
    (p k : Nat) [NeZero p] (port : Fin k)
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) :
    kt19SelectedPortLabelEquiv p k port left =
      kt19SingleSiteLabel
        (ZMod.finEquiv p (left (kt19SelectedPortCoordinate p k port))) := by
  funext site
  have hsite : site = default := Subsingleton.elim _ _
  subst site
  rfl
private theorem kt19SingleSiteLabel_registerPairing
    (p : Nat) [NeZero p] (a x : ZMod p) :
    registerPairing p (kt19SingleSiteLabel a) (kt19SingleSiteLabel x) = a * x := by
  unfold registerPairing
  rw [Fintype.sum_unique]
  rfl
private theorem kt19SingleSiteLabel_cubicExponent
    (p : Nat) [NeZero p] (x : ZMod p) :
    cubicExponent p (kt19SingleSiteLabel x) = x ^ 3 := by
  unfold cubicExponent
  rw [Fintype.sum_unique]
  rfl
private theorem kt19SelectedPortMagicExponent_cross
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k))
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    (registerPairing p label
        ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
          ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right))) +
      cubicExponent p
        ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
          ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)))) +
      (registerPairing p (kt19SingleSiteLabel (label port))
          (kt19SelectedPortLabelEquiv p k port
            (kt19SelectedPortZeroLabel p k port)) +
        cubicExponent p (kt19SelectedPortLabelEquiv p k port
          (kt19SelectedPortZeroLabel p k port))) =
      (registerPairing p (kt19SingleSiteLabel (label port))
          (kt19SelectedPortLabelEquiv p k port left) +
        cubicExponent p (kt19SelectedPortLabelEquiv p k port left)) +
      (registerPairing p label
          ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
            ((kt19SelectedPortSubsystem p k port).recombineLabel
              (kt19SelectedPortZeroLabel p k port, right))) +
        cubicExponent p
          ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
            ((kt19SelectedPortSubsystem p k port).recombineLabel
              (kt19SelectedPortZeroLabel p k port, right)))) := by
  rw [kt19SelectedPortLabelEquiv_eq_singleSiteLabel p k port left,
    kt19SelectedPortLabelEquiv_eq_singleSiteLabel p k port
      (kt19SelectedPortZeroLabel p k port)]
  rw [kt19SingleSiteLabel_registerPairing, kt19SingleSiteLabel_cubicExponent,
    kt19SingleSiteLabel_registerPairing, kt19SingleSiteLabel_cubicExponent]
  rw [kt19RegisterPairing_split_port p k port label
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right))),
    kt19CubicExponent_split_port p k port
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right))),
    kt19RegisterPairing_split_port p k port label
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right))),
    kt19CubicExponent_split_port p k port
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right)))]
  rw [kt19PrimeQuditLabelEquiv_symm_recombine_apply_port p k port left right,
    kt19PrimeQuditLabelEquiv_symm_recombine_zero_apply_port p k port right]
  simp_rw [kt19PrimeQuditLabelEquiv_symm_recombine_apply_ne p k port left right,
    kt19PrimeQuditLabelEquiv_symm_recombine_apply_ne p k port
      (kt19SelectedPortZeroLabel p k port) right]
  simp [kt19SelectedPortZeroLabel, Qudit.zeroLabel]
  ring
private theorem kt19Phase_cross_product
    (p : Nat) [NeZero p] (globalScale localScale : Complex)
    (globalLeft localZero localLeft globalZero : ZMod p)
    (hphaseExponent : globalLeft + localZero = localLeft + globalZero) :
    (globalScale * phase p globalLeft) * (localScale * phase p localZero) =
      (localScale * phase p localLeft) * (globalScale * phase p globalZero) := by
  have hphase : phase p globalLeft * phase p localZero =
      phase p localLeft * phase p globalZero := by
    rw [← phase_add, hphaseExponent, phase_add]
  calc
    (globalScale * phase p globalLeft) * (localScale * phase p localZero) =
        (globalScale * localScale) *
          (phase p globalLeft * phase p localZero) := by ring
    _ = (globalScale * localScale) *
          (phase p localLeft * phase p globalZero) := by rw [hphase]
    _ = (localScale * phase p localLeft) *
          (globalScale * phase p globalZero) := by ring
private theorem kt19SelectedPortMagicState_recombine_amplitude
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k))
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label)).ofLp
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)) =
      (kt19SelectedPortMagicState p k port label).ofLp left *
        (kt19SelectedPortComplementState p k port label).ofLp right := by
  simp only [kt19SelectedPortComplementState, WithLp.ofLp_toLp]
  field_simp [kt19SelectedPortMagicState_zero_ne_zero p k port label]
  simpa only [kt19SelectedPortMagicState, kt19SelectedPortTransport_symm_apply,
    kt19PrimeQuditRegisterQuditTransport_apply, magicRegisterKet_apply] using
    (kt19Phase_cross_product p _ _ _ _ _ _
      (kt19SelectedPortMagicExponent_cross p k port label left right))
private theorem kt19SelectedPortMagicState_factorization
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortSubsystem p k port).registerFactorization
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label)) =
      kt19SelectedPortMagicState p k port label ⊗ₜ[Complex]
        kt19SelectedPortComplementState p k port label := by
  apply (kt19SelectedPortSubsystem p k port).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_apply_apply]
  ext labels
  change ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
      (magicRegisterKet p label)) labels =
    (kt19SelectedPortSubsystem p k port).registerFactorization.symm
      (kt19SelectedPortMagicState p k port label ⊗ₜ[Complex]
        kt19SelectedPortComplementState p k port label) labels
  rw [kt19SelectedPortRegisterFactorization_symm_tmul_apply]
  have hsplit :
      (kt19SelectedPortSubsystem p k port).recombineLabel
          ((kt19SelectedPortSubsystem p k port).splitLabel labels) = labels :=
    (kt19SelectedPortSubsystem p k port).recombine_splitLabel labels
  calc
    ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label)) labels =
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label))
          ((kt19SelectedPortSubsystem p k port).recombineLabel
            ((kt19SelectedPortSubsystem p k port).splitLabel labels)) := by rw [hsplit]
    _ = (kt19SelectedPortMagicState p k port label)
          ((kt19SelectedPortSubsystem p k port).splitLabel labels).1 *
        (kt19SelectedPortComplementState p k port label)
          ((kt19SelectedPortSubsystem p k port).splitLabel labels).2 := by
          exact kt19SelectedPortMagicState_recombine_amplitude p k port label
            ((kt19SelectedPortSubsystem p k port).splitLabel labels).1
            ((kt19SelectedPortSubsystem p k port).splitLabel labels).2
private theorem kt19SelectedPortMagicState_inner_self
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    inner Complex (kt19SelectedPortMagicState p k port label)
      (kt19SelectedPortMagicState p k port label) = 1 := by
  rw [kt19SelectedPortMagicState]
  calc
    inner Complex
        ((kt19SelectedPortTransport p k port).symm
          (magicRegisterKet p (kt19SingleSiteLabel (label port))))
        ((kt19SelectedPortTransport p k port).symm
          (magicRegisterKet p (kt19SingleSiteLabel (label port)))) =
      inner Complex
        ((kt19SelectedPortTransport p k port)
          ((kt19SelectedPortTransport p k port).symm
            (magicRegisterKet p (kt19SingleSiteLabel (label port)))))
        ((kt19SelectedPortTransport p k port)
          ((kt19SelectedPortTransport p k port).symm
            (magicRegisterKet p (kt19SingleSiteLabel (label port))))) :=
          ((kt19SelectedPortTransport p k port).map_inner _ _).symm
    _ = inner Complex (magicRegisterKet p (kt19SingleSiteLabel (label port)))
        (magicRegisterKet p (kt19SingleSiteLabel (label port))) := by
          simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
          rfl
    _ = 1 := magicRegisterKet_inner_self p (kt19SingleSiteLabel (label port))
private theorem kt19SelectedPortComplementState_inner_self
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    inner Complex (kt19SelectedPortComplementState p k port label)
      (kt19SelectedPortComplementState p k port label) = 1 := by
  have hglobal : inner Complex
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label))
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label)) = 1 := by
    rw [(kt19PrimeQuditRegisterQuditTransport p (Fin k)).map_inner]
    exact magicRegisterKet_inner_self p label
  have hfactorNorm : inner Complex
      ((kt19SelectedPortSubsystem p k port).registerFactorization
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label)))
      ((kt19SelectedPortSubsystem p k port).registerFactorization
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label))) = 1 := by
    rw [(kt19SelectedPortSubsystem p k port).registerFactorization.map_inner]
    exact hglobal
  rw [kt19SelectedPortMagicState_factorization, TensorProduct.inner_tmul,
    kt19SelectedPortMagicState_inner_self, one_mul] at hfactorNorm
  exact hfactorNorm
private theorem kt19SelectedPort_partialTrace_pure_magicWord
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortTransport p k port).conjDensity
      ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
          (DensityOperator.pureDensity (magicRegisterKet p label) (by
            rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
              magicRegisterKet_inner_self]
            norm_num)))) =
      DensityOperator.pureDensity
        (magicRegisterKet p (kt19SingleSiteLabel (label port))) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num) := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    QuditSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, QuditSubsystem.selectedPartialTrace,
    DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne
    (kt19PrimeQuditRegisterQuditTransport p (Fin k))]
  rw [QuditSubsystem.conjOperator_rankOne
    (kt19SelectedPortSubsystem p k port).registerFactorization]
  rw [kt19SelectedPortMagicState_factorization]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [kt19SelectedPortComplementState_inner_self]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne (kt19SelectedPortTransport p k port)]
  rw [kt19SelectedPortMagicState]
  simpa only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
private theorem kt19SelectedPortActualMarginal_toOperator
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    (kt19SelectedPortActualMarginal family mu hmu_nonneg hmu_sum port).toOperator =
      kt19SelectedPortTransportedChannel p k port
        (family.run mu hmu_nonneg hmu_sum).acceptedOutput.toOperator :=
  rfl
private theorem kt19SelectedPortTransportedChannel_pure_magicWord
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    kt19SelectedPortTransportedChannel p k port
        (DensityOperator.pureDensity (magicRegisterKet p label) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num)).toOperator =
      (kt19SelectedPortMagicWordDensity p (label port)).toOperator := by
  change
    ((kt19SelectedPortTransport p k port).conjDensity
      ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
          (DensityOperator.pureDensity (magicRegisterKet p label) (by
            rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
              magicRegisterKet_inner_self]
            norm_num))))).toOperator = _
  simpa only [kt19SelectedPortMagicWordDensity] using
    congrArg DensityOperator.toOperator
      (kt19SelectedPort_partialTrace_pure_magicWord p k port label)
private theorem kt19SelectedPortSingleSite_wordProbability
    (p : Nat) [NeZero p] (nu : ZMod p → ℝ) (a : ZMod p) :
    wordProbability p nu (kt19SingleSiteLabel a) = nu a := by
  unfold wordProbability kt19SingleSiteLabel
  rw [Fintype.prod_unique]
  rfl
private theorem kt19SelectedPortSingleSiteResource_toOperator
    (p : Nat) [NeZero p] (nu : ZMod p → ℝ)
    (hnu_nonneg : ∀ a : ZMod p, 0 ≤ nu a)
    (hnu_sum : ∑ a : ZMod p, nu a = 1) :
    (kt19SingleSiteResource nu hnu_nonneg hnu_sum).toOperator =
      ∑ a : ZMod p, (nu a : Complex) •
        (kt19SelectedPortMagicWordDensity p a).toOperator := by
  unfold kt19SingleSiteResource magicRegisterResource
  rw [DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  symm
  apply Fintype.sum_equiv (kt19SelectedPortSingleSiteLabelEquiv p)
  intro a
  change
    (nu a : Complex) • (kt19SelectedPortMagicWordDensity p a).toOperator =
      (wordProbability p nu (kt19SingleSiteLabel a) : Complex) •
        (kt19SelectedPortMagicWordDensity p a).toOperator
  rw [kt19SelectedPortSingleSite_wordProbability]
private theorem kt19SelectedPortLabelDistribution_eq_routedPortMass_div_success
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k)
    (heps : kt19ErrorRate mu < 1) (a : ZMod p) :
    kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port a =
      kt19SelectedPortRoutedMass family mu port a /
        kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
  classical
  unfold kt19SelectedPortLabelDistribution
  simp_rw [KT19DistillationFamily.outputLabelDistribution_eq_routedMass_div_success
    family mu hmu_nonneg hmu_sum heps]
  calc
    (∑ label : PrimeQuditRegisterLabel p (Fin k),
        if label port = a then
          KT19DistillationFamily.routedAcceptedMass family mu label /
            kt19Success family.rowFamily mu hmu_nonneg hmu_sum
        else 0) =
        (∑ label : PrimeQuditRegisterLabel p (Fin k),
          if label port = a then
            KT19DistillationFamily.routedAcceptedMass family mu label else 0) /
          kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro label _
            by_cases hlabel : label port = a <;> simp [hlabel]
    _ = kt19SelectedPortRoutedMass family mu port a /
          kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
      congr 1
      unfold KT19DistillationFamily.routedAcceptedMass kt19SelectedPortRoutedMass
      calc
        (∑ label : PrimeQuditRegisterLabel p (Fin k),
          if label port = a then
            ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
              if kt19AcceptedWord family.rowFamily error ∧
                  label = KT19DistillationFamily.kt19Routing family error then
                wordProbability p mu error
              else 0
          else 0) =
          ∑ label : PrimeQuditRegisterLabel p (Fin k),
            ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
              if label port = a then
                if kt19AcceptedWord family.rowFamily error ∧
                    label = KT19DistillationFamily.kt19Routing family error then
                  wordProbability p mu error
                else 0
              else 0 := by
                apply Finset.sum_congr rfl
                intro label _
                by_cases hlabel : label port = a <;> simp [hlabel]
        _ = ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
            ∑ label : PrimeQuditRegisterLabel p (Fin k),
              if label port = a then
                if kt19AcceptedWord family.rowFamily error ∧
                    label = KT19DistillationFamily.kt19Routing family error then
                  wordProbability p mu error
                else 0
              else 0 := Finset.sum_comm
        _ = ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
            if kt19AcceptedWord family.rowFamily error ∧
                KT19DistillationFamily.kt19Routing family error port = a then
              wordProbability p mu error
            else 0 := by
              apply Finset.sum_congr rfl
              intro error _
              by_cases haccepted : kt19AcceptedWord family.rowFamily error
              · rw [Fintype.sum_eq_single
                    (KT19DistillationFamily.kt19Routing family error)]
                · simp [haccepted]
                · intro label hne
                  simp [hne]
              · simp [haccepted]
private theorem kt19SelectedPort_routedWordSum_grouped
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (port : Fin k) :
    (∑ error : Word (ZMod p) (KeptPunctureLocation p k),
      if kt19AcceptedWord family.rowFamily error then
        (wordProbability p mu error : Complex) •
          (kt19SelectedPortMagicWordDensity p
            (KT19DistillationFamily.kt19Routing family error port)).toOperator
      else 0) =
      ∑ a : ZMod p, (kt19SelectedPortRoutedMass family mu port a : Complex) •
        (kt19SelectedPortMagicWordDensity p a).toOperator := by
  classical
  calc
    (∑ error : Word (ZMod p) (KeptPunctureLocation p k),
      if kt19AcceptedWord family.rowFamily error then
        (wordProbability p mu error : Complex) •
          (kt19SelectedPortMagicWordDensity p
            (KT19DistillationFamily.kt19Routing family error port)).toOperator
      else 0) =
        ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
          ∑ a : ZMod p,
            if kt19AcceptedWord family.rowFamily error ∧
                KT19DistillationFamily.kt19Routing family error port = a then
              (wordProbability p mu error : Complex) •
                (kt19SelectedPortMagicWordDensity p a).toOperator
            else 0 := by
              apply Finset.sum_congr rfl
              intro error _
              by_cases haccepted : kt19AcceptedWord family.rowFamily error
              · rw [Fintype.sum_eq_single
                    (KT19DistillationFamily.kt19Routing family error port)]
                · simp [haccepted]
                · intro a hne
                  have hroute : ¬ (kt19AcceptedWord family.rowFamily error ∧
                      KT19DistillationFamily.kt19Routing family error port = a) := by
                    intro hroute
                    exact hne hroute.2.symm
                  rw [if_neg hroute]
              · simp [haccepted]
    _ = ∑ a : ZMod p,
          ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
            if kt19AcceptedWord family.rowFamily error ∧
                KT19DistillationFamily.kt19Routing family error port = a then
              (wordProbability p mu error : Complex) •
                (kt19SelectedPortMagicWordDensity p a).toOperator
            else 0 := Finset.sum_comm
    _ = ∑ a : ZMod p, (kt19SelectedPortRoutedMass family mu port a : Complex) •
          (kt19SelectedPortMagicWordDensity p a).toOperator := by
            apply Finset.sum_congr rfl
            intro a _
            unfold kt19SelectedPortRoutedMass
            rw [Complex.ofReal_sum, Finset.sum_smul]
            apply Finset.sum_congr rfl
            intro error _
            split <;> simp
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
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
universe u
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
namespace QEC.Distillation.KT19VanishingOverhead
theorem _root_.solution
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k)
    (heps : kt19ErrorRate mu < 1) :
    kt19SelectedPortDensity family mu hmu_nonneg hmu_sum port =
      kt19SingleSiteResource
        (kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port)
        (kt19SelectedPortLabelDistribution_nonneg family mu hmu_nonneg hmu_sum port)
        (kt19SelectedPortLabelDistribution_sum family mu hmu_nonneg hmu_sum port) := by
  apply DensityOperator.ext_toOperator
  rw [kt19SelectedPortDensity_eq_actualMarginal,
    kt19SelectedPortActualMarginal_toOperator,
    KT19DistillationFamily.acceptedOutput_toOperator_eq_routed_sum
      family mu hmu_nonneg hmu_sum heps]
  simp only [map_smul, map_sum, apply_ite, map_zero]
  simp_rw [kt19SelectedPortTransportedChannel_pure_magicWord]
  rw [kt19SelectedPort_routedWordSum_grouped]
  rw [kt19SelectedPortSingleSiteResource_toOperator]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [kt19SelectedPortLabelDistribution_eq_routedPortMass_div_success
    family mu hmu_nonneg hmu_sum port heps a]
  simp only [smul_smul, Complex.ofReal_div, div_eq_mul_inv]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : Complex)) (mul_comm _ _)
end QEC.Distillation.KT19VanishingOverhead

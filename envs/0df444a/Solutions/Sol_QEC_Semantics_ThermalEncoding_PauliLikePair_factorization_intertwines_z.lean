-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.factorization_intertwines_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:58:47.122149+00:00
-- url     : https://prove2.me/submissions/5453a852-fad4-4398-a67f-d371953ab625

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution
    (v : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    P.factorization (P.tensorPauliZ v) = P.z (P.factorization v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
      change P.factorizationLinearEquiv (P.tensorPauliZ (q ⊗ₜ[Complex] a)) =
        P.z (P.factorizationLinearEquiv (q ⊗ₜ[Complex] a))
      rw [P.tensorPauliZ_tmul, P.factorizationLinearEquiv_tmul,
        P.factorizationLinearEquiv_tmul]
      have ha : P.z (a : H) = a :=
        (P.auxiliary_mem_iff (a : H)).1 a.property
      have hxa : P.z (P.x (a : H)) = -P.x (a : H) :=
        (P.negative_mem_iff (P.x (a : H))).1 (P.xAuxToNegative a).property
      simp [Qubit.pauliZ_apply, Qubit.zPhase, ha, hxa]
  | add first second hfirst hsecond =>
      simp only [map_add, hfirst, hsecond]
end QEC.Semantics.ThermalEncoding.PauliLikePair

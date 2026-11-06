-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.registerFactorization_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:12:29.505013+00:00
-- url     : https://prove2.me/submissions/7ddbb399-8bf5-4ec2-8c73-7c8f9ee447a3

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring ι) :
    S.registerFactorization (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex bits) =
      (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex
        (S.splitBitstring bits).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex
        (S.splitBitstring bits).2) := by
  dsimp [registerFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [bitstringFactorization]
end QEC.Semantics.FiniteSubsystem

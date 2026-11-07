-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerProjector_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:50:55.897191+00:00
-- url     : https://prove2.me/submissions/ae225dc3-3e39-4867-8e99-6fb7bf623b88

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerProjector_fixed_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
private theorem jointStabilizerProjector_mul_factor
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerProjector checks hcomm syndrome := by
  classical
  let reduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome (Finset.univ.erase check))
  have hfactor : reduced * jointStabilizerFactor checks syndrome check =
      jointStabilizerProjector checks hcomm syndrome := by
    simpa [reduced, jointStabilizerProjector] using
      (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
        (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ))
  calc
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerFactor checks syndrome check =
        (reduced * jointStabilizerFactor checks syndrome check) *
          jointStabilizerFactor checks syndrome check := by rw [hfactor]
    _ = reduced *
        (jointStabilizerFactor checks syndrome check *
          jointStabilizerFactor checks syndrome check) := by rw [mul_assoc]
    _ = reduced * jointStabilizerFactor checks syndrome check := by
        rw [jointStabilizerFactor_idempotent]
    _ = jointStabilizerProjector checks hcomm syndrome := hfactor
private theorem jointStabilizerFactor_mul_jointStabilizerProjector
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerFactor checks syndrome check *
        jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome := by
  have hcommProduct : Commute (jointStabilizerFactor checks syndrome check)
      (jointStabilizerProjector checks hcomm syndrome) := by
    unfold jointStabilizerProjector
    exact Finset.noncommProd_commute Finset.univ
      (jointStabilizerFactor checks syndrome)
      (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)
      (jointStabilizerFactor checks syndrome check)
      (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
  rw [hcommProduct.eq]
  exact jointStabilizerProjector_mul_factor checks hcomm syndrome check
private theorem jointStabilizerProjector_apply_eq_self_of_factor_fixed
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (psi : Qubit.QubitRegister ι)
    (hfixed : ∀ check, jointStabilizerFactor checks syndrome check psi = psi) :
    jointStabilizerProjector checks hcomm syndrome psi = psi := by
  unfold jointStabilizerProjector
  refine Finset.noncommProd_induction Finset.univ
    (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)
    (fun product => product psi = psi) ?_ ?_ ?_
  · intro A B hA hB
    simp only [Module.End.mul_apply, hB, hA]
  · rfl
  · intro check _
    exact hfixed check
end PauliSymplectic
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (psi : Qubit.QubitRegister ι) :
    jointStabilizerProjector checks hcomm syndrome psi = psi ↔
      ∀ check, toHermitianQubitOperator (checks check) psi =
        (syndrome check).sign • psi := by
  constructor
  · intro hfixed check
    apply (stabilizerProjector_fixed_iff (checks check) (syndrome check) psi).1
    have hfactor := congrArg (fun operator : Operator (Qubit.QubitRegister ι) => operator psi)
      (jointStabilizerFactor_mul_jointStabilizerProjector checks hcomm syndrome check)
    change jointStabilizerFactor checks syndrome check
        (jointStabilizerProjector checks hcomm syndrome psi) =
      jointStabilizerProjector checks hcomm syndrome psi at hfactor
    calc
      jointStabilizerFactor checks syndrome check psi =
          jointStabilizerFactor checks syndrome check
            (jointStabilizerProjector checks hcomm syndrome psi) := by rw [hfixed]
      _ = jointStabilizerProjector checks hcomm syndrome psi := hfactor
      _ = psi := hfixed
  · intro heigen
    apply jointStabilizerProjector_apply_eq_self_of_factor_fixed checks hcomm syndrome psi
    intro check
    exact (stabilizerProjector_fixed_iff (checks check) (syndrome check) psi).2 (heigen check)
end QEC.Coding.PauliSymplectic

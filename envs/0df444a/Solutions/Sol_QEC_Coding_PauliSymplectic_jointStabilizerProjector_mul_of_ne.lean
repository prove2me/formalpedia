-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerProjector_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:49:54.665173+00:00
-- url     : https://prove2.me/submissions/d85aa29b-1770-48b0-b74d-c7a8a63414dc

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerProjector_mul_opposite
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
private theorem StabilizerOutcome.eq_opposite_of_ne
    (left right : StabilizerOutcome) (hne : left ≠ right) :
    right = left.opposite := by
  cases left <;> cases right <;>
    simp [StabilizerOutcome.opposite] at hne ⊢
private theorem jointStabilizerProjector_erase_mul
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    (Finset.univ.erase check).noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome (Finset.univ.erase check)) *
      jointStabilizerFactor checks syndrome check =
        jointStabilizerProjector checks hcomm syndrome := by
  classical
  simpa [jointStabilizerProjector] using
    (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
      (jointStabilizerFactor checks syndrome)
      (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ))
private theorem exists_check_of_jointSyndrome_ne
    (left right : JointSyndrome κ) (hne : left ≠ right) :
    ∃ check, left check ≠ right check := by
  classical
  by_contra hnone
  push_neg at hnone
  exact hne (funext hnone)
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
    (syndromeLeft syndromeRight : JointSyndrome κ) (hne : syndromeLeft ≠ syndromeRight) :
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight = 0 := by
  classical
  obtain ⟨check, hcheck⟩ :=
    exists_check_of_jointSyndrome_ne syndromeLeft syndromeRight hne
  have hopposite : syndromeRight check = (syndromeLeft check).opposite :=
    StabilizerOutcome.eq_opposite_of_ne (syndromeLeft check) (syndromeRight check) hcheck
  let leftReduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndromeLeft)
    (jointStabilizerFactor_pairwise checks hcomm syndromeLeft (Finset.univ.erase check))
  let rightReduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndromeRight)
    (jointStabilizerFactor_pairwise checks hcomm syndromeRight (Finset.univ.erase check))
  have hleftFactor : leftReduced * jointStabilizerFactor checks syndromeLeft check =
      jointStabilizerProjector checks hcomm syndromeLeft := by
    exact jointStabilizerProjector_erase_mul checks hcomm syndromeLeft check
  have hrightFactor : rightReduced * jointStabilizerFactor checks syndromeRight check =
      jointStabilizerProjector checks hcomm syndromeRight := by
    exact jointStabilizerProjector_erase_mul checks hcomm syndromeRight check
  have hcross : Commute (jointStabilizerFactor checks syndromeLeft check) rightReduced := by
    dsimp [rightReduced]
    exact Finset.noncommProd_commute (Finset.univ.erase check)
      (jointStabilizerFactor checks syndromeRight)
      (jointStabilizerFactor_pairwise checks hcomm syndromeRight (Finset.univ.erase check))
      (jointStabilizerFactor checks syndromeLeft check)
      (fun other _ =>
        jointStabilizerFactor_commute checks hcomm check other syndromeLeft syndromeRight)
  have hsingle : jointStabilizerFactor checks syndromeLeft check *
      jointStabilizerFactor checks syndromeRight check = 0 := by
    change stabilizerProjector (checks check) (syndromeLeft check) *
        stabilizerProjector (checks check) (syndromeRight check) = 0
    rw [hopposite]
    exact stabilizerProjector_mul_opposite (checks check) (syndromeLeft check)
  calc
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight =
        (leftReduced * jointStabilizerFactor checks syndromeLeft check) *
          (rightReduced * jointStabilizerFactor checks syndromeRight check) := by
            rw [hleftFactor, hrightFactor]
    _ = leftReduced *
        (jointStabilizerFactor checks syndromeLeft check * rightReduced) *
          jointStabilizerFactor checks syndromeRight check := by
            simp only [mul_assoc]
    _ = leftReduced *
        (rightReduced * jointStabilizerFactor checks syndromeLeft check) *
          jointStabilizerFactor checks syndromeRight check := by
            rw [hcross.eq]
    _ = (leftReduced * rightReduced) *
        (jointStabilizerFactor checks syndromeLeft check *
          jointStabilizerFactor checks syndromeRight check) := by
            simp only [mul_assoc]
    _ = 0 := by rw [hsingle, mul_zero]
end QEC.Coding.PauliSymplectic

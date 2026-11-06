-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerSyndrome_map_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:09:04.083955+00:00
-- url     : https://prove2.me/submissions/bcd01740-fa40-4cbd-836d-47ce3c80e20d

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_inStabilizerNormalizer_iff_commutes_generators
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryMul_upToSign_binaryMul_dagger_left
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_zero_iff_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_of_binaryUpToSign
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
namespace Semantics
namespace Qubit
open Classical
open scoped BigOperators
universe u
variable {ι : Type u}
variable [Fintype ι] [DecidableEq ι]
end Qubit
end Semantics
namespace Coding
open Classical
open scoped BigOperators
universe u w
namespace PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι] in
/-- The finite generator syndrome is additive under binary Pauli multiplication. -/
private theorem stabilizerSyndrome_binaryMul
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (A B : Binary ι) :
    stabilizerSyndrome generators (binaryMul A B) =
      stabilizerSyndrome generators A + stabilizerSyndrome generators B := by
  funext j
  simp only [stabilizerSyndrome_apply, Pi.add_apply, stabilizerSyndromeBit,
    binaryMul, symplecticForm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring
end PauliSymplectic
namespace ChainComplexData
end ChainComplexData
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E A B : Binary ι) :
    (stabilizerSyndrome generators E = 0 ↔
      InStabilizerNormalizer generators E) ∧
    (stabilizerSyndrome generators A = stabilizerSyndrome generators B ↔
      stabilizerSyndrome generators (binaryMul A B) = 0) ∧
    stabilizerSyndrome generators (binaryMul A B) =
      stabilizerSyndrome generators (binaryMul (binaryDagger A) B) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hZero
      apply (inStabilizerNormalizer_iff_commutes_generators generators E).2
      intro j
      apply (stabilizerSyndromeBit_eq_zero_iff_commutes (generators j) E).1
      simpa [stabilizerSyndrome] using congrFun hZero j
    · intro hNormalizer
      funext j
      exact (stabilizerSyndromeBit_eq_zero_iff_commutes (generators j) E).2
        ((inStabilizerNormalizer_iff_commutes_generators generators E).1
          hNormalizer j)
  · rw [stabilizerSyndrome_binaryMul]
    constructor
    · intro hEqual
      rw [hEqual]
      funext j
      exact CharTwo.add_self_eq_zero _
    · intro hSum
      funext j
      apply CharTwo.add_eq_zero.mp
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun hSum j
  · funext j
    exact stabilizerSyndromeBit_eq_of_binaryUpToSign
      (binaryMul_upToSign_binaryMul_dagger_left A B)
end QEC.Coding.PauliSymplectic

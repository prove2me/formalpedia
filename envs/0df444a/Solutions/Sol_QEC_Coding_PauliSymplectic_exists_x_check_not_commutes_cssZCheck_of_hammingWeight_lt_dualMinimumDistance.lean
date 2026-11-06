-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:20:04.803232+00:00
-- url     : https://prove2.me/submissions/17df552b-3ccf-4960-b049-836bbfd4953a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_not_mem_carrier_of_hammingWeight_lt_minimumDistance
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
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
    (xCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    ∃ x, x ∈ xCode.carrier ∧ ¬ Commutes (cssZCheck z) (cssXCheck x) := by
  have hzNotDual : z ∉ xCode.dual.carrier :=
    not_mem_carrier_of_hammingWeight_lt_minimumDistance (C := xCode.dual) hminZ hz0 hzlt
  rcases exists_carrier_wordPairing_ne_zero_of_not_mem_dual xCode hzNotDual with
    ⟨x, hx, hpair⟩
  refine ⟨x, hx, ?_⟩
  intro hcomm
  have hrev :
      symplecticForm
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι)
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι) = 0 := by
    simpa [cssZCheck, cssXCheck, Commutes] using hcomm
  have hrev_eq :
      symplecticForm
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι)
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι) =
        -symplecticForm
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) := by
    simp [symplecticForm, mul_comm]
  have hsymp :
      symplecticForm
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0 := by
    have hneg :
        -symplecticForm
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0 := by
      rwa [← hrev_eq]
    exact neg_eq_zero.mp hneg
  have hpairXZ : wordPairing (F := ZMod 2) (ι := ι) x z = 0 := by
    simpa [symplecticForm_x_zero_zero_z_eq_wordPairing] using hsymp
  exact hpair (by
    simpa [wordPairing_apply, dotProduct_comm] using hpairXZ)
end QEC.Coding.PauliSymplectic

-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:22.631823+00:00
-- url     : https://prove2.me/submissions/b321822c-d406-4351-9c03-a42a6d16deca

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_xPart_le_weight
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_zPart_le_weight
import Theorems.Thm_QEC_Coding_PauliSymplectic_exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
import Theorems.Thm_QEC_Coding_PauliSymplectic_exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
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
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι) {dX dZ : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    {P : Binary ι}
    (hP : P.vector.xPart ≠ 0 ∨ P.vector.zPart ≠ 0)
    (hwt : weight P < min dX dZ) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) P := by
  rcases hP with hx0 | hz0
  · have hxltMin : HammingWeight P.vector.xPart < min dX dZ :=
      lt_of_le_of_lt (hammingWeight_xPart_le_weight P) hwt
    have hxlt : HammingWeight P.vector.xPart < dX :=
      lt_of_lt_of_le hxltMin (Nat.min_le_left dX dZ)
    rcases
        exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
          zCode hminX hx0 hxlt with
      ⟨z, hz, hnotCommutes⟩
    refine ⟨cssZCheck z, Or.inr ⟨z, hz, rfl⟩, ?_⟩
    intro hcomm
    exact hnotCommutes (by
      simpa [cssXCheck, cssZCheck, Commutes, symplecticForm] using hcomm)
  · have hzltMin : HammingWeight P.vector.zPart < min dX dZ :=
      lt_of_le_of_lt (hammingWeight_zPart_le_weight P) hwt
    have hzlt : HammingWeight P.vector.zPart < dZ :=
      lt_of_lt_of_le hzltMin (Nat.min_le_right dX dZ)
    rcases
        exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
          xCode hminZ hz0 hzlt with
      ⟨x, hx, hnotCommutes⟩
    refine ⟨cssXCheck x, Or.inl ⟨x, hx, rfl⟩, ?_⟩
    intro hcomm
    exact hnotCommutes (by
      simpa [cssZCheck, cssXCheck, Commutes, symplecticForm] using hcomm)
end QEC.Coding.PauliSymplectic

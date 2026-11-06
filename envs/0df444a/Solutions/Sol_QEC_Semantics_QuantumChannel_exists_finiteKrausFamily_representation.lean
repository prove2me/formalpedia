-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.exists_finiteKrausFamily_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:55.662073+00:00
-- url     : https://prove2.me/submissions/b4bf1834-d0b2-4146-a18c-0b0470e5f65c

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_complete_of_inducedMap_trace_preserving
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_stdChoiMatrix_posSemidef_of_completelyPositive
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
open QEC.Semantics.QuantumChannel
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (Φ : QuantumChannel H K) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.Complete ∧ R.inducedMap = Φ.toLinearMap := by
  classical
  rcases exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef Φ.toLinearMap
      (stdChoiMatrix_posSemidef_of_completelyPositive Φ.toLinearMap Φ.completely_positive) with
    ⟨m, R, hRmap⟩
  refine ⟨m, R, ?_, hRmap⟩
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [hRmap]
  simpa using Φ.trace_map A
end QEC.Semantics.QuantumChannel

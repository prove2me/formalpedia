-- Prove2me | solution 1 for QEC.Semantics.FiniteAlphabet.detectableOn_transport_of_localOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:17:23.960088+00:00
-- url     : https://prove2.me/submissions/c4b31051-2d59-4abe-b37a-e91af7a9e879

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.FiniteAlphabet
open scoped BigOperators TensorProduct
universe u
variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]
attribute [local instance] QEC.Semantics.FiniteAlphabet._p2m_local_instance_ac378d2a8a_23
variable {A I}
namespace QEC.Semantics.FiniteAlphabet
theorem _root_.solution
    (C : QuantumCode (EuclideanSpace Complex (I → A)))
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (h : DetectableOn C (localOperator S E)) :
    DetectableOn (C.transport (registerUnitary A I)) (S.extendLocalToRegister E) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rintro x ⟨x₀, hx, rfl⟩ y ⟨y₀, hy, rfl⟩
  change inner Complex (registerUnitary A I x₀)
      (S.extendLocalToRegister E (registerUnitary A I y₀)) =
    c * inner Complex (registerUnitary A I x₀) (registerUnitary A I y₀)
  have hE : registerUnitary A I (localOperator S E y₀) =
      S.extendLocalToRegister E (registerUnitary A I y₀) := by
    simp [localOperator, UnitaryTransport.conjOperator, UnitaryTransport.symm]
  rw [← hE, (registerUnitary A I).map_inner, (registerUnitary A I).map_inner]
  exact hc x₀ hx y₀ hy
end QEC.Semantics.FiniteAlphabet

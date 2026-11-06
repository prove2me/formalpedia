-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.scale_complete_of_adjoint_square_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:07:52.858506+00:00
-- url     : https://prove2.me/submissions/8bc9dbca-383d-444c-a768-6b223eb8ed9d

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H K) (amp : ι → Complex)
    (h : ∑ i : ι, (star (amp i) * amp i) •
          ((LinearMap.adjoint (E.operator i)).comp (E.operator i)) = 1) :
    (E.scale amp).Complete := by
  classical
  unfold Complete scale
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _hi
  have hAdj :
      LinearMap.adjoint (amp i • E.operator i) =
        star (amp i) • LinearMap.adjoint (E.operator i) := by
    exact
      map_smulₛₗ
        (LinearMap.adjoint : (H →ₗ[Complex] K) ≃ₗ⋆[Complex] (K →ₗ[Complex] H))
        (amp i) (E.operator i)
  rw [hAdj]
  ext x
  simp [LinearMap.comp_apply, smul_smul, mul_comm]
end QEC.Semantics.FiniteKrausFamily

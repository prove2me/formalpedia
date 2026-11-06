-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:39:05.718853+00:00
-- url     : https://prove2.me/submissions/b53be989-80e9-4ce2-9973-2e9eb3efc3bf

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_idempotent
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    IndexedKnillLaflammeProjectorConditionWithScalar E C scalar := by
  intro i j
  ext v
  apply ext_inner_left Complex
  intro w
  have hinnerP :
      inner Complex (C.projector w) (C.projector v) =
        inner Complex w (C.projector v) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w (C.projector v)
    have hIdemV : C.projector (C.projector v) = C.projector v := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun A : Operator H => A v) C.projector_idempotent
    simpa [C.projector_adjoint_eq_self, hIdemV] using hAdj.symm
  calc
    inner Complex w
        (((C.projector.comp ((LinearMap.adjoint (E.operator i)).comp
          (E.operator j))).comp C.projector) v)
        = inner Complex (C.projector w)
            (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
              (C.projector v)) := by
          have hAdj :=
            LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w
              (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
                (C.projector v))
          simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self] using hAdj
    _ = inner Complex (E.operator i (C.projector w))
          (E.operator j (C.projector v)) := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) (E.operator i)
              (C.projector w) (E.operator j (C.projector v)))
    _ = scalar i j * inner Complex (C.projector w) (C.projector v) :=
          h i j (C.projector w) (C.projector_mem_carrier w)
            (C.projector v) (C.projector_mem_carrier v)
    _ = scalar i j * inner Complex w (C.projector v) := by
          rw [hinnerP]
    _ = inner Complex w ((scalar i j • C.projector) v) := by
          simp
end QEC.Semantics.FiniteKrausFamily

-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_of_indexedProjectorConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:39:23.959227+00:00
-- url     : https://prove2.me/submissions/a6effd70-0229-49bb-ad0b-3b24f12008bc

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
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
    (h : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    IndexedKnillLaflammeConditionWithScalar E C scalar := by
  intro i j x hx y hy
  have hxP : C.projector x = x := C.projector_eq_self_of_mem hx
  have hyP : C.projector y = y := C.projector_eq_self_of_mem hy
  have hInsert :
      inner Complex x ((LinearMap.adjoint (E.operator i)) (E.operator j y)) =
        inner Complex x
          (C.projector (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
            (C.projector y))) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector x
        (((LinearMap.adjoint (E.operator i)).comp (E.operator j)) (C.projector y))
    simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self, hxP, hyP] using
      hAdj.symm
  calc
    inner Complex (E.operator i x) (E.operator j y)
        = inner Complex x ((LinearMap.adjoint (E.operator i)) (E.operator j y)) := by
          simpa using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) (E.operator i) x
              (E.operator j y)).symm
    _ = inner Complex x
          (C.projector (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
            (C.projector y))) :=
          hInsert
    _ = inner Complex x ((scalar i j • C.projector) y) := by
          simpa [LinearMap.comp_apply, hyP] using
            congrArg (fun z : H => inner Complex x z)
              (congrArg (fun A : Operator H => A y) (h i j))
    _ = scalar i j * inner Complex x y := by
          simp [hyP]
end QEC.Semantics.FiniteKrausFamily

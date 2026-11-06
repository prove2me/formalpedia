-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.matrixConditionWithScalar_of_indexedConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:08.563382+00:00
-- url     : https://prove2.me/submissions/1b81ec83-ea6f-46c4-ba9d-048986738142

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_mem_sameSpaceErrorSet_iff
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
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
    KnillLaflammeMatrixConditionWithScalar C E.sameSpaceErrorSet
      (sameSpaceScalar E scalar) := by
  classical
  intro A hA B hB x hx y hy
  let i : ι := Classical.choose ((E.mem_sameSpaceErrorSet_iff A).1 hA)
  let j : ι := Classical.choose ((E.mem_sameSpaceErrorSet_iff B).1 hB)
  have hAi : E.operator i = A := by
    dsimp [i]
    exact Classical.choose_spec ((E.mem_sameSpaceErrorSet_iff A).1 hA)
  have hBj : E.operator j = B := by
    dsimp [j]
    exact Classical.choose_spec ((E.mem_sameSpaceErrorSet_iff B).1 hB)
  have hscalar : sameSpaceScalar E scalar A B = scalar i j := by
    simp [sameSpaceScalar, hA, hB, i, j]
  calc
    inner Complex (A x) (B y)
        = inner Complex (E.operator i x) (E.operator j y) := by
          rw [← hAi, ← hBj]
    _ = scalar i j * inner Complex x y := h i j x hx y hy
    _ = sameSpaceScalar E scalar A B * inner Complex x y := by
          rw [hscalar]
end QEC.Semantics.FiniteKrausFamily

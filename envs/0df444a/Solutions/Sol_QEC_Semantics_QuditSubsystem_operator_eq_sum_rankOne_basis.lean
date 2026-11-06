-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.operator_eq_sum_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:11:34.125873+00:00
-- url     : https://prove2.me/submissions/65aba039-8c14-4981-9a65-4c58df862553

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
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
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ,
      (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
  have hId : (LinearMap.id : Operator H) = ∑ i : κ,
      (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by
    ext x
    simpa using
      congrArg (fun f : H →L[Complex] H => f x)
        (OrthonormalBasis.sum_rankOne_eq_id b).symm
  calc
    A = A.comp (LinearMap.id : Operator H) := by rfl
    _ = A.comp (∑ i : κ,
        (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap) := by rw [hId]
    _ = ∑ i : κ,
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
      ext x
      simp [InnerProductSpace.rankOne_apply]
end QEC.Semantics.QuditSubsystem

-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.operator_scalar_on_code_of_forall_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:14:11.619025+00:00
-- url     : https://prove2.me/submissions/9262a74d-c9d7-4280-b4a7-bf5a70853307

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (A : Operator H) (C : QuantumCode H)
    (hline : ∀ (x : H), x ∈ C.carrier → A x ∈ Complex ∙ x) :
    ∃ scalar : Complex, ∀ (x : H), x ∈ C.carrier → A x = scalar • x := by
  classical
  let fC : C.carrier →ₗ[Complex] C.carrier :=
    { toFun := fun x => ⟨A (x : H), by
        rcases Submodule.mem_span_singleton.mp (hline (x : H) x.prop) with ⟨a, ha⟩
        rw [← ha]
        exact C.carrier.smul_mem a x.prop⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact A.map_add (x : H) (y : H)
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact A.map_smul a (x : H) }
  have hdep : ∀ v : C.carrier, ¬ LinearIndependent Complex ![v, fC v] := by
    intro v
    have hvspan : fC v ∈ Complex ∙ v := by
      rcases Submodule.mem_span_singleton.mp (hline (v : H) v.prop) with ⟨a, ha⟩
      exact Submodule.mem_span_singleton.mpr ⟨a, by
        apply Subtype.ext
        simpa [fC] using ha⟩
    intro hli
    rw [linearIndependent_fin2] at hli
    rcases Submodule.mem_span_singleton.mp hvspan with ⟨a, ha⟩
    by_cases ha0 : a = 0
    · have hfzero : fC v = 0 := by
        rw [← ha, ha0, zero_smul]
      exact hli.1 hfzero
    · have hv_eq : a⁻¹ • fC v = v := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      exact hli.2 a⁻¹ hv_eq
  rcases LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := fC) hdep with
    ⟨scalar, hscalar⟩
  refine ⟨scalar, ?_⟩
  intro x hx
  have happly := congrArg (fun f : C.carrier →ₗ[Complex] C.carrier => f ⟨x, hx⟩) hscalar
  have happly_val := congrArg Subtype.val happly
  simpa [fC] using happly_val
end QEC.Semantics.FiniteKrausFamily

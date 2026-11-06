-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.sum_log_selectedDimensions_le_card_mul_log_uniformDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:12.032103+00:00
-- url     : https://prove2.me/submissions/9957ad95-8bc0-4d97-954a-33c2e9750aac

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
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
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (hq : forall i, 0 < q i) (D : Nat)
    (hD : forall i, i ∈ S.selected -> q i <= D) :
    (∑ i ∈ S.selected, Real.logb 2 (q i : Real)) <=
      (S.selected.card : Real) * Real.logb 2 (D : Real) := by
  calc
    (∑ i ∈ S.selected, Real.logb 2 (q i : Real)) <=
        ∑ i ∈ S.selected, Real.logb 2 (D : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hq i)
        (by exact_mod_cast hD i hi)
    _ = (S.selected.card : Real) * Real.logb 2 (D : Real) := by
      simp [nsmul_eq_mul]
end QEC.Semantics.QuditSubsystem

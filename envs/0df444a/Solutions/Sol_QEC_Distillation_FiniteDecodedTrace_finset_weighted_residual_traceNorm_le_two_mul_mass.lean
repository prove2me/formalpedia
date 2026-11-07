-- Prove2me | solution 1 for QEC.Distillation.FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:38.234551+00:00
-- url     : https://prove2.me/submissions/7bbc7a81-7e1e-4262-bc3e-5b7148b0969c

import Definitions.Def_QEC_Distillation_Core_FiniteCentering
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_smul
import Theorems.Thm_QEC_Semantics_traceNorm_sum_le
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteDecodedTrace
open Semantics
open scoped BigOperators
universe u v
namespace QEC.Distillation.FiniteDecodedTrace
theorem _root_.solution
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (indices : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm (∑ i ∈ indices,
        if selected i then (weight i : Complex) • (branch i - center) else 0) ≤
      ∑ i ∈ indices, if selected i then 2 * weight i else 0 := by
  classical
  calc
    traceNorm (∑ i ∈ indices,
        if selected i then (weight i : Complex) • (branch i - center) else 0) ≤
      ∑ i ∈ indices, traceNorm
        (if selected i then (weight i : Complex) • (branch i - center) else 0) := by
          simpa using traceNorm_sum_le indices (fun i : ι =>
            if selected i then (weight i : Complex) • (branch i - center) else 0)
    _ ≤ ∑ i ∈ indices, if selected i then 2 * weight i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hselected : selected i
      · simp only [if_pos hselected, traceNorm_smul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight i)]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hbranch i) (hweight i)
      · simp only [if_neg hselected]
        exact le_of_eq (by rw [traceNorm_eq_zero_iff])
end QEC.Distillation.FiniteDecodedTrace

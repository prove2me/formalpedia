-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.weighted_residual_traceNorm_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:21:00.667848+00:00
-- url     : https://prove2.me/submissions/63a8e111-c251-4952-9b72-f5fbc7d4db2f

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_finset_weighted_residual_traceNorm_le_two_mul_mass
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u v w
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (support : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (residual : Operator H) (residualMass : ℝ)
    (hresidual : residual = support.sum (fun i =>
      if selected i then (weight i : Complex) • (branch i - center) else 0))
    (hmass : residualMass = support.sum (fun i =>
      if selected i then weight i else 0))
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm residual ≤ 2 * residualMass := by
  rw [hresidual, hmass]
  calc
    traceNorm (support.sum (fun i =>
        if selected i then (weight i : Complex) • (branch i - center) else 0)) ≤
        support.sum (fun i => if selected i then 2 * weight i else 0) := by
      simpa [mul_comm] using
        FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
          support weight selected branch center hweight hbranch
    _ = 2 * support.sum (fun i => if selected i then weight i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hselected : selected i <;> simp [hselected]
end QEC.Distillation.HH18Parameterized

-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.complex_of_real_sum_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:50.45628+00:00
-- url     : https://prove2.me/submissions/8b14109b-619a-45d0-973c-b7aacc69f394

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
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
    {ι : Type u} [DecidableEq ι] (support : Finset ι)
    (mass : ℝ) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected]
    (hmass : mass = support.sum (fun i =>
      if selected i then weight i else 0)) :
    (mass : Complex) = support.sum (fun i =>
      if selected i then (weight i : Complex) else 0) := by
  rw [hmass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hselected : selected i <;> simp [hselected]
end QEC.Distillation.HH18Parameterized

-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.linearMap_apply_selected_sum_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:53.54426+00:00
-- url     : https://prove2.me/submissions/f683fe04-f346-4eb0-8871-fa7c00eac0dc

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
    {ι : Type u} [DecidableEq ι] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (support : Finset ι) (linearMap : Operator H →ₗ[Complex] Operator K)
    (input : Operator H) (weight : ι → Complex) (selected : ι → Prop)
    [DecidablePred selected] (inputBranch : ι → Operator H)
    (outputBranch : ι → Operator K)
    (hinput : input = support.sum (fun i =>
      if selected i then weight i • inputBranch i else 0))
    (hpointwise : ∀ i, linearMap (inputBranch i) = outputBranch i) :
    linearMap input = support.sum (fun i =>
      if selected i then weight i • outputBranch i else 0) := by
  rw [hinput, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hselected : selected i
  · simp only [if_pos hselected]
    rw [map_smul, hpointwise i]
  · simp only [if_neg hselected, map_zero]
end QEC.Distillation.HH18Parameterized

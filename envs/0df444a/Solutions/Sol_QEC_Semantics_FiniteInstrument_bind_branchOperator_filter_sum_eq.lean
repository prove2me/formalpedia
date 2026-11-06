-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bind_branchOperator_filter_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:00:37.291543+00:00
-- url     : https://prove2.me/submissions/32101dc7-6c41-45eb-8500-155b52233944

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_branchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K)
    (J : Omega -> FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Omega -> Xi -> Prop)
    [∀ firstOutcome, DecidablePred (secondPredicate firstOutcome)]
    (A : Operator H) :
    (∑ outcome : Sigma fun _ : Omega => Xi,
      if firstPredicate outcome.1 ∧
          secondPredicate outcome.1 outcome.2 then
        (I.bind (fun firstOutcome => J firstOutcome)).branchOperator outcome A
      else 0) =
      ∑ firstOutcome : Omega,
        if firstPredicate firstOutcome then
          ∑ secondOutcome : Xi,
            if secondPredicate firstOutcome secondOutcome then
              (J firstOutcome).branchOperator secondOutcome
                (I.branchOperator firstOutcome A)
            else 0
        else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro firstOutcome _
  by_cases hfirst : firstPredicate firstOutcome
  · rw [if_pos hfirst]
    apply Finset.sum_congr rfl
    intro secondOutcome _
    by_cases hsecond : secondPredicate firstOutcome secondOutcome
    · rw [if_pos hsecond, if_pos ⟨hfirst, hsecond⟩]
      exact bind_branchOperator I (fun firstOutcome => J firstOutcome)
        firstOutcome secondOutcome A
    · simp [hsecond]
  · simp [hfirst]
end QEC.Semantics.FiniteInstrument

-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerAccepted_shortage_iff_no_full_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:26.487128+00:00
-- url     : https://prove2.me/submissions/0d264950-0239-49b2-a4bc-24f074190fa1

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_mem
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedSelector_injective
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


attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution {α : Type v}
    (accepts : α → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory α attempts) (required : Nat) :
    (tensorPowerAcceptedIndices accepts attempts history).card < required ↔
      ¬ ∃ selection : Fin required → Fin attempts,
        Function.Injective selection ∧
          ∀ slot, selection slot ∈ tensorPowerAcceptedIndices accepts attempts history := by
  constructor
  · intro hshort hselection
    rcases hselection with ⟨selection, hInjective, hAccepted⟩
    let selected : Fin required → {trial // trial ∈ tensorPowerAcceptedIndices accepts attempts history} :=
      fun slot => ⟨selection slot, hAccepted slot⟩
    have hSelectedInjective : Function.Injective selected := by
      intro first second heq
      apply hInjective
      exact Subtype.ext_iff.mp heq
    have hcard : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_le_of_injective selected hSelectedInjective
    exact (Nat.not_le_of_lt hshort) hcard
  · intro hnone
    by_contra hnot
    have hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card :=
      Nat.le_of_not_lt hnot
    apply hnone
    refine ⟨tensorPowerAcceptedSelector accepts attempts history required hrequired, ?_, ?_⟩
    · exact tensorPowerAcceptedSelector_injective accepts attempts history required hrequired
    · intro slot
      exact tensorPowerAcceptedSelector_mem accepts attempts history required hrequired slot
end QEC.Semantics.FiniteInstrument

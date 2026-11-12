-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.nestedTensorHistoryAll_ne_true_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:06:23.6263+00:00
-- url     : https://prove2.me/submissions/dbac74ee-be5f-43f1-a9b5-f337b7102af5

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Theorems.Thm_QEC_Distillation_HH18Parameterized_nestedTensorHistoryAll_eq_true_iff

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {alpha : Type*}
    (predicate : alpha -> Bool) (branches depth : Nat)
    (history : nestedTensorHistory alpha branches depth) :
    nestedTensorHistoryAll predicate branches depth history ≠ true ↔
      ∃ path : nestedTensorPath branches depth,
        predicate (nestedTensorHistoryAt alpha branches depth history path) ≠ true := by
  constructor
  · intro hfailure
    by_contra hnoWitness
    apply hfailure
    apply (nestedTensorHistoryAll_eq_true_iff
      predicate branches depth history).2
    intro path
    by_contra hpath
    exact hnoWitness ⟨path, hpath⟩
  · rintro ⟨path, hpath⟩ hall
    exact hpath
      ((nestedTensorHistoryAll_eq_true_iff
        predicate branches depth history).1 hall path)
end QEC.Distillation.HH18Parameterized

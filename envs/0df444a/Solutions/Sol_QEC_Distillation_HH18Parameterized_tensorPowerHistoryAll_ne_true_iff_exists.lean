-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.tensorPowerHistoryAll_ne_true_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:07:45.93995+00:00
-- url     : https://prove2.me/submissions/d3dfb353-af02-4d26-95d4-87f6fe5983d0

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Theorems.Thm_QEC_Distillation_HH18Parameterized_tensorPowerHistoryAll_eq_true_iff

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
    (predicate : alpha -> Bool) (attempts : Nat)
    (history : tensorPowerHistory alpha attempts) :
    tensorPowerHistoryAll predicate attempts history ≠ true ↔
      ∃ trial : Fin attempts,
        predicate (tensorPowerHistoryAt alpha attempts history trial) ≠ true := by
  constructor
  · intro hfailure
    by_contra hnoWitness
    apply hfailure
    apply (tensorPowerHistoryAll_eq_true_iff predicate attempts history).2
    intro trial
    by_contra htrial
    exact hnoWitness ⟨trial, htrial⟩
  · rintro ⟨trial, htrial⟩ hall
    exact htrial
      ((tensorPowerHistoryAll_eq_true_iff predicate attempts history).1 hall trial)
end QEC.Distillation.HH18Parameterized

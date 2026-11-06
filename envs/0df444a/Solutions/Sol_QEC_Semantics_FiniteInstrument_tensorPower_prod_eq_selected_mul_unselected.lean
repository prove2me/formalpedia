-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_prod_eq_selected_mul_unselected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:07:06.204213+00:00
-- url     : https://prove2.me/submissions/2f407641-6e15-407b-8d90-ea96fc2cf5b5

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (f : Fin attempts → Complex) :
    (∏ trial : Fin attempts, f trial) =
      (∏ slot : Fin required,
        f (tensorPowerAcceptedSelector accepts attempts history required hrequired
          slot)) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        f trial.1 := by
  let splitEquiv := tensorPowerSelectedAndUnselectedTrialEquiv accepts attempts
    history required hrequired
  calc
    (∏ trial : Fin attempts, f trial) =
        ∏ index : Fin required ⊕
            tensorPowerUnselectedTrial accepts attempts history required hrequired,
          f (splitEquiv index) := by
      exact (Fintype.prod_equiv splitEquiv
        (fun index => f (splitEquiv index)) f (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      rfl
end QEC.Semantics.FiniteInstrument

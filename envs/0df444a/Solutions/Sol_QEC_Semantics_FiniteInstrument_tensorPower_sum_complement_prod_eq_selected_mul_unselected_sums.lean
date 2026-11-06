-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:11:51.388251+00:00
-- url     : https://prove2.me/submissions/e9307ded-6cd1-4238-a140-a0095182fb53

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_prod_eq_selected_mul_unselected
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_sum_complement_prod_unselected


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
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (entry : Fin attempts → Qubit.Bitstring ι → Qubit.Bitstring ι → Complex)
    (left right : Qubit.Bitstring (Fin required × ι)) :
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : Fin attempts,
        entry trial
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (left, complement)) trial)
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (right, complement)) trial)) =
      (∏ slot : Fin required,
        entry
          (tensorPowerAcceptedSelector accepts attempts history required hrequired
            slot)
          (fun port => left (slot, port))
          (fun port => right (slot, port))) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        ∑ bits : Qubit.Bitstring ι, entry trial.1 bits bits := by
  calc
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : Fin attempts,
        entry trial
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (left, complement)) trial)
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (right, complement)) trial)) =
        ∑ complement : Qubit.Bitstring
            (tensorPowerSelectedSubsystem accepts attempts history required
              hrequired ι).ComplementCoordinates,
          ((∏ slot : Fin required,
            entry
              (tensorPowerAcceptedSelector accepts attempts history required
                hrequired slot)
              (fun port => left (slot, port))
              (fun port => right (slot, port))) *
          ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
              hrequired,
            entry trial.1
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)) := by
      apply Finset.sum_congr rfl
      intro complement _
      rw [tensorPower_prod_eq_selected_mul_unselected accepts attempts history
        required hrequired]
      congr 1
      · apply Finset.prod_congr rfl
        intro slot _
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
          accepts attempts history required hrequired ι left complement slot]
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_selected
          accepts attempts history required hrequired ι right complement slot]
      · apply Finset.prod_congr rfl
        intro trial _
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
          accepts attempts history required hrequired ι left complement trial]
        rw [tensorPowerSelectedHistoryBitstringEquiv_symm_historyAt_unselected
          accepts attempts history required hrequired ι right complement trial]
    _ =
        (∏ slot : Fin required,
          entry
            (tensorPowerAcceptedSelector accepts attempts history required
              hrequired slot)
            (fun port => left (slot, port))
            (fun port => right (slot, port))) *
        (∑ complement : Qubit.Bitstring
            (tensorPowerSelectedSubsystem accepts attempts history required
              hrequired ι).ComplementCoordinates,
          ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
              hrequired,
            entry trial.1
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)
              (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts
                history required hrequired ι complement trial)) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [tensorPower_sum_complement_prod_unselected accepts attempts history
        required hrequired ι (fun trial bits => entry trial.1 bits bits)]
end QEC.Semantics.FiniteInstrument

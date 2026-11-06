-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:14:22.700746+00:00
-- url     : https://prove2.me/submissions/9cbf2c1e-7706-44b7-815b-21a714d65d25

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    (tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι basisHistory).2 =
        tensorPowerSelectedComplementBitstring accepts attempts observedHistory required
          hrequired ι basisHistory := by
  rfl
end QEC.Semantics.FiniteInstrument

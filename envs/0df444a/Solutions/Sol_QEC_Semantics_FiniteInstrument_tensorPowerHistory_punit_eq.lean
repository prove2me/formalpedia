-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistory_punit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:02:22.565264+00:00
-- url     : https://prove2.me/submissions/cb1d54fd-26ee-4a95-8781-36fe9c264836

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution :
    ∀ (attempts : Nat) (history : tensorPowerHistory PUnit attempts),
      history = tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit) := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      exact PUnit.ext _ _
  | succ attempts ih =>
      rintro ⟨head, tail⟩
      cases head
      change (PUnit.unit, tail) =
        (PUnit.unit, tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit))
      rw [ih tail]
end QEC.Semantics.FiniteInstrument

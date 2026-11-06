-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerHistoryAt_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:02:15.925199+00:00
-- url     : https://prove2.me/submissions/ffc0776c-1d76-41d4-bf5f-942fcbcd9cfd

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {beta gamma : Type u} (mapIndex : beta → gamma) :
    ∀ attempts (history : tensorPowerHistory beta attempts)
      (trial : Fin attempts),
      tensorPowerHistoryAt gamma attempts
          (tensorPowerHistoryMap mapIndex attempts history) trial =
        mapIndex (tensorPowerHistoryAt beta attempts history trial) := by
  intro attempts
  induction attempts with
  | zero =>
      intro history trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro history trial
      rcases history with ⟨head, tail⟩
      refine Fin.cases ?_ ?_ trial
      · rfl
      · intro tailTrial
        exact ih tail tailTrial
end QEC.Semantics.FiniteInstrument

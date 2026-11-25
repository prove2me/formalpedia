-- Prove2me | solution 1 for PI.LevelKSplit.W.Meas.measurableSet_borel_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:56.473625+00:00
-- url     : https://prove2.me/submissions/980e250d-5436-4c7c-91dc-73ec635de3ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CompVInvMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasurableSetBorelOfIsClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Meas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
namespace PI.LevelKSplit.W.Meas
theorem _root_.solution {X : Type} [TopologicalSpace X] {s : Set X}
    (h : IsClosed s) : MeasurableSet[borel X] s := by
  have : MeasurableSet[borel X] sᶜ := MeasurableSpace.measurableSet_generateFrom h.isOpen_compl
  simpa using this.compl
end PI.LevelKSplit.W.Meas

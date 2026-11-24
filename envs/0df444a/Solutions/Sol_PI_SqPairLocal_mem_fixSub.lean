-- Prove2me | solution 1 for PI.SqPairLocal.mem_fixSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:16.139899+00:00
-- url     : https://prove2.me/submissions/708f5d74-768d-45b3-aa22-2478b5c51a42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
namespace PI.SqPairLocal
theorem _root_.solution {R : Type} [CommRing R] (σ : R ≃+* R) (x : R) : x ∈ fixSub σ ↔ σ x = x :=
  Iff.rfl
end PI.SqPairLocal

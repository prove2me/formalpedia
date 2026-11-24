-- Prove2me | solution 1 for PI.SqPairLocal.FixD.isUnit_iff_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:34.090384+00:00
-- url     : https://prove2.me/submissions/a8ffb4bb-77c1-4388-886d-a1ae4bf2471f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)
namespace PI.SqPairLocal.FixD
theorem _root_.solution (x : fixSub σ) : IsUnit x ↔ IsUnit (x : R) :=
  ⟨fun h => h.map (fixSub σ).subtype, isUnit_sub σ⟩
end PI.SqPairLocal.FixD

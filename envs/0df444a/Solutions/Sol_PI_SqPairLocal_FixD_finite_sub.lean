-- Prove2me | solution 1 for PI.SqPairLocal.FixD.finite_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:03.087193+00:00
-- url     : https://prove2.me/submissions/05eda9b8-f405-4ef7-9db4-113247223d44

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
theorem _root_.solution [IsLocalRing R] [IsLocalRing (fixSub σ)] [Finite (ResidueField R)] :
    Finite (ResidueField (fixSub σ)) :=
  Finite.of_injective _ (IsLocalRing.ResidueField.map (fixSub σ).subtype).injective
end PI.SqPairLocal.FixD

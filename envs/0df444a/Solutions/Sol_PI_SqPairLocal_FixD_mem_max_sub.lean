-- Prove2me | solution 1 for PI.SqPairLocal.FixD.mem_max_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:07.832366+00:00
-- url     : https://prove2.me/submissions/c0d1dcf9-1f82-4796-a939-5efa864c779b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
import Theorems.Thm_PI_SqPairLocal_FixD_isUnit_iff_sub

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
theorem _root_.solution [IsLocalRing R] [IsLocalRing (fixSub σ)] (x : fixSub σ) :
    x ∈ maximalIdeal (fixSub σ) ↔ (x : R) ∈ maximalIdeal R := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_sub]
end PI.SqPairLocal.FixD

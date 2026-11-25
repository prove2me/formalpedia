-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.length_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:21.276951+00:00
-- url     : https://prove2.me/submissions/72362a2a-58b4-4a24-ba49-7009ec6665d8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P : Submodule R M} (h : P ≤ N) : Module.length R (↥P ⧸ N.comap P.subtype) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact h (a - b).2
end PI.UnitaryGroupMassFormula.BallQuotLen

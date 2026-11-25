-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.ballO_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:40.48813+00:00
-- url     : https://prove2.me/submissions/52c60bf3-899f-4e24-afa8-c79ec87dba8b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ball_mono


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
variable {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V] {e : V}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {c c' : Pts O A → ℤ} (hc : ∀ ζ, c ζ ≤ c' ζ) : ballO ϖ e c ≤ ballO ϖ e c' := fun v hv => ball_mono h he hc hv
end PI.UnitaryGroupMassFormula.BallQuotLen

-- Prove2me | solution 1 for PositivityTheory.ThKF0.Split.splitE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:31.530609+00:00
-- url     : https://prove2.me/submissions/e450711c-7c37-47cd-b7b4-836d18f8600e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory
open scoped ENNReal Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Split
variable (F : Type) [Field F] [NumberField F] (κ : Type)
namespace PositivityTheory.ThKF0.Split
theorem _root_.solution (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl
end PositivityTheory.ThKF0.Split

-- Prove2me | solution 1 for PositivityTheory.ThKF0.Split.continuous_splitE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:07.656767+00:00
-- url     : https://prove2.me/submissions/9f2d3308-be82-4e65-804f-852ca220485e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSplit
import Theorems.Thm_PositivityTheory_ThKF0_Split_continuous_ofMixed

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
theorem _root_.solution : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  exact continuous_pi fun i => ((continuous_ofMixed F).comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)
end PositivityTheory.ThKF0.Split

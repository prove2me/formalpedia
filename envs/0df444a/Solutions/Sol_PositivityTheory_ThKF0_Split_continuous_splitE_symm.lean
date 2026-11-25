-- Prove2me | solution 1 for PositivityTheory.ThKF0.Split.continuous_splitE_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:37.711235+00:00
-- url     : https://prove2.me/submissions/7199bc76-9076-4ba2-a5ef-0b9eb2088773

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSplit
import Theorems.Thm_PositivityTheory_ThKF0_Split_continuous_toMixed

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
theorem _root_.solution : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  exact (continuous_pi fun i => (continuous_toMixed F).comp
    (continuous_fst.comp (continuous_apply i))).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
end PositivityTheory.ThKF0.Split

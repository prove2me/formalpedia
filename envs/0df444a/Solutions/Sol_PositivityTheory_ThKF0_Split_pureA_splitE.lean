-- Prove2me | solution 1 for PositivityTheory.ThKF0.Split.pureA_splitE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:52.478927+00:00
-- url     : https://prove2.me/submissions/028f884e-7cd6-4da4-9160-c56bb9a1d4bb

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSplit
import Theorems.Thm_PositivityTheory_ThKF0_Split_splitE_apply

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
theorem _root_.solution (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]
end PositivityTheory.ThKF0.Split

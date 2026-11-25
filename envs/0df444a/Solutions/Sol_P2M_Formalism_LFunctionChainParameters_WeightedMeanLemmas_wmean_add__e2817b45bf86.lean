-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_add__e2817b45bf86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:50.491543+00:00
-- url     : https://prove2.me/submissions/d4b336ec-b0f6-4fda-8425-d106b9303e3d

import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
variable {ι : Type*} [Fintype ι]
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas
theorem _root_.solution (d X Y : ι → ℝ) :
    wmean d (fun u => X u + Y u) = wmean d X + wmean d Y := by
  unfold wmean
  rw [← add_div, ← Finset.sum_add_distrib]
  simp only [mul_add]
end Formalism.LFunctionChainParameters.WeightedMeanLemmas

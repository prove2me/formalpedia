-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_mono__ee8853d08dcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:57.424059+00:00
-- url     : https://prove2.me/submissions/2123db51-386a-401d-8ec3-ff5ee7abc439

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
theorem _root_.solution [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ u, 0 < d u)
    (hXY : ∀ u, X u ≤ Y u) : wmean d X ≤ wmean d Y := by
  unfold wmean
  have hS : 0 < ∑ u, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hXY u) (hd u).le) hS.le
end Formalism.LFunctionChainParameters.WeightedMeanLemmas

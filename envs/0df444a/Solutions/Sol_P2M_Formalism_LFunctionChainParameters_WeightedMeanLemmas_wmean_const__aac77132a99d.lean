-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_const__aac77132a99d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:51.451508+00:00
-- url     : https://prove2.me/submissions/94ac0f8b-63e4-4b45-93e4-990ec751b221

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
theorem _root_.solution [Nonempty ι] {d : ι → ℝ} (hd : ∀ u, 0 < d u) (c : ℝ) :
    wmean d (fun _ => c) = c := by
  unfold wmean
  have hS : 0 < ∑ u, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  rw [← Finset.sum_mul, mul_div_cancel_left₀ _ hS.ne']
end Formalism.LFunctionChainParameters.WeightedMeanLemmas

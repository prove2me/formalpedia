-- Prove2me | solution 1 for TwoDegenerateGraphs.choose_le_exp_binary_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/dcec0ece-2234-4910-9a49-630c986fe691

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_log_choose_le_binary_entropy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    (trialCount.choose successCount : ℝ) ≤
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ))) := by
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  exact (Real.log_le_iff_le_exp hchoose).mp
    (log_choose_le_binary_entropy trialCount successCount hcount)
end TwoDegenerateGraphs

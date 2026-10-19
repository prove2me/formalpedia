-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryEntropy_tau_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/b15f99f8-0196-4b94-a783-fc23af006be5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_tau_lt_one_half

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution : binaryEntropy tau < 1 := by
  have htau_ne : tau ≠ (2 : ℝ)⁻¹ := by
    intro heq
    have hlt := tau_lt_one_half
    rw [heq] at hlt
    norm_num at hlt
  unfold binaryEntropy
  apply (div_lt_iff₀ log_two_pos).mpr
  simpa using (Real.binEntropy_lt_log_two.mpr htau_ne)
end TwoDegenerateGraphs

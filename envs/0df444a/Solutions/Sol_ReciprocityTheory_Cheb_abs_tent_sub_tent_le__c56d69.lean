-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_tent_sub_tent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:07.655789+00:00
-- url     : https://prove2.me/submissions/c9411903-6488-4582-b4c5-5cfb2a2ef6b4

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (s t : ℝ) : |tent s - tent t| ≤ |s - t| := by
  unfold tent
  calc |max 0 (1 - |s|) - max 0 (1 - |t|)| ≤ |(1 - |s|) - (1 - |t|)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = |(|t| - |s|)| := by ring_nf
    _ ≤ |t - s| := abs_abs_sub_abs_le_abs_sub t s
    _ = |s - t| := abs_sub_comm t s
end ReciprocityTheory.Cheb

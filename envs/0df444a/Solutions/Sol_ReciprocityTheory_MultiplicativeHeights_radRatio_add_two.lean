-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.radRatio_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:01.534374+00:00
-- url     : https://prove2.me/submissions/c44a67ae-8fde-4dc1-aeb7-28e4e02dd782

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_pos
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_add_two
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radK_add_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    radK (k + 2) / radJ (k + 2) = radK k / radJ k + 1 / ((k : ℝ) + 1) := by
  have hJ := radJ_pos k
  rw [radK_add_two hk, radJ_add_two]
  field_simp
end ReciprocityTheory.MultiplicativeHeights

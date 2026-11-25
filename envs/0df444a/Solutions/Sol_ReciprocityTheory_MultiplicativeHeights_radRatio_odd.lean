-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.radRatio_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:52.310746+00:00
-- url     : https://prove2.me/submissions/19110c8c-0e4f-40cc-938b-45fd3ab01272

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radRatio_add_two

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
theorem _root_.solution (m : ℕ) :
    radK (2 * m + 1) / radJ (2 * m + 1) = radK 1 / radJ 1 + (harmonic m : ℝ) / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h := radRatio_add_two (k := 2 * n + 1) (by omega)
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, h, ih, harmonic_succ]
    push_cast
    field_simp
    ring
end ReciprocityTheory.MultiplicativeHeights

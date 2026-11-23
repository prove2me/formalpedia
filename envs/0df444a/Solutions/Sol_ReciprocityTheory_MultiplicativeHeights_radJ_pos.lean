-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.radJ_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:25.411113+00:00
-- url     : https://prove2.me/submissions/811216fd-9c85-49eb-8f61-b80b4d770c41

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_eq

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
theorem _root_.solution (k : ℕ) : 0 < radJ k := by
  rw [radJ_eq]
  exact div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos
end ReciprocityTheory.MultiplicativeHeights

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hyp_inhabited_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:50.658694+00:00
-- url     : https://prove2.me/submissions/a9d81cfd-7947-49ef-87e9-c2f848b6797f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory
open scoped Laplacian
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : ∃ u : ℂ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ u 0 = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)⟩
end ReciprocityTheory.AnForm.A

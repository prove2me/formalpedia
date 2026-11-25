-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:18:27.385186+00:00
-- url     : https://prove2.me/submissions/6f810dd4-4995-4e2e-9673-9fb89b57ab86

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_bump_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_bump_le_one
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_of_le_half
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_of_one_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_one_ge
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_chi_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
open ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
namespace ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
theorem _root_.solution : IsCutoff chi := by
  have hI : 0 < prim 1 := by linarith [prim_one_ge]
  refine ⟨contDiff_const.sub (prim_contDiff.div_const _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [chi, prim_of_le_half ht]
  · intro t ht
    simp [chi, prim_of_one_le ht, hI.ne']
  · intro t
    have h0 : 0 ≤ prim t / prim 1 := div_nonneg (prim_nonneg t) hI.le
    have h1 : prim t / prim 1 ≤ 1 := (div_le_one hI).2 (prim_le t)
    constructor <;> simp only [chi] <;> linarith
  · intro t
    rw [(chi_hasDerivAt t).deriv, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg t) hI.le),
      div_le_iff₀ hI]
    nlinarith [bump_le_one t, prim_one_ge]
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff

-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inv_of_InG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:37.58603+00:00
-- url     : https://prove2.me/submissions/f9bad056-2529-4db7-aec2-7ada69da2f3d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_JJ_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {x : M2 n} (hx : InG x) : -(JJ n * xᴴ * JJ n) * x = 1 := by
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h, JJ_mul_self, neg_neg]
end PositivityTheory.Rg.Sw.LVs

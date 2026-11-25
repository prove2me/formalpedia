-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.mul_J_mul_of_InG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:44.658095+00:00
-- url     : https://prove2.me/submissions/0a38f9a3-8fd6-4907-bfab-c64554ab297b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_JJ_mul_self
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_InG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_eq_of_InG

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
theorem _root_.solution {x : M2 n} (hx : InG x) : x * JJ n * xᴴ = JJ n := by
  have h1 : x * -(JJ n * xᴴ * JJ n) = 1 := by
    rw [← inv_eq_of_InG hx]; exact Matrix.mul_nonsing_inv x (isUnit_det_of_InG hx)
  calc x * JJ n * xᴴ = x * JJ n * xᴴ * (JJ n * JJ n) * (-1) := by
        rw [JJ_mul_self]; simp
    _ = (x * -(JJ n * xᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one]
    _ = JJ n := by rw [h1, Matrix.one_mul]
end PositivityTheory.Rg.Sw.LVs

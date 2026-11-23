-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.sum_smul_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:44.51747+00:00
-- url     : https://prove2.me/submissions/7b76d8fb-00e7-408e-a342-5ee92540c10e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) :
    ∑ l, c l • b l = ∑ j, nu b c j • gs b j := by
  calc ∑ l, c l • b l = ∑ l, ∑ j, (c l * mu b l j) • gs b j := by
        refine Finset.sum_congr rfl fun l _ => ?_
        conv_lhs => rw [b_eq_sum b hb l]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    _ = ∑ j, nu b c j • gs b j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [nu, Finset.sum_smul]
end ReciprocityTheory.ReducedBases.T2

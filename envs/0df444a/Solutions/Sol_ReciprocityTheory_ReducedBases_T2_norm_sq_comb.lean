-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.norm_sq_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:44.336652+00:00
-- url     : https://prove2.me/submissions/7d002135-6231-4432-96f0-9f0af6c88862

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_sum_smul_b
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_sum

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
    ‖∑ l, c l • b l‖ ^ 2 = ∑ j, nu b c j ^ 2 * ‖gs b j‖ ^ 2 := by
  rw [sum_smul_b b hb c, ← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, inner_gs_sum]
  ring
end ReciprocityTheory.ReducedBases.T2

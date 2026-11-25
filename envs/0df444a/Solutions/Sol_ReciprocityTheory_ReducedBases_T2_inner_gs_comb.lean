-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.inner_gs_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:54.533976+00:00
-- url     : https://prove2.me/submissions/6b1e407c-e1a7-42e9-90d3-8dba45bc1cea

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
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ l, c l • b l⟫_ℝ = nu b c j * ‖gs b j‖ ^ 2 := by
  rw [sum_smul_b b hb c, inner_gs_sum]
end ReciprocityTheory.ReducedBases.T2

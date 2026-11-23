-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.inner_gs_b_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:18.86691+00:00
-- url     : https://prove2.me/submissions/2bf8063c-8952-4138-8830-9e0eb6baa755

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_span

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
theorem _root_.solution (b : Fin d → E) (k : Fin d) : ⟪gs b k, b k⟫_ℝ = ‖gs b k‖ ^ 2 := by
  have h0 := inner_gs_span b k (b_sub_gs_mem b k)
  rw [inner_sub_right, sub_eq_zero] at h0
  rw [h0, real_inner_self_eq_norm_sq]
end ReciprocityTheory.ReducedBases.T2

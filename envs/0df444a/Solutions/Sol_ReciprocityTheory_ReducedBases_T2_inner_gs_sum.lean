-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.inner_gs_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:18.822034+00:00
-- url     : https://prove2.me/submissions/f4d3b1e5-1282-43fa-ad3e-914e003d15f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_orth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
private lemma inner_gs_sum_smul_gs (b : Fin d → E) (x : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ k, x k • gs b k⟫_ℝ = x j * ‖gs b j‖ ^ 2 := by
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  · intro k _ hk
    rw [real_inner_smul_right, gs_orth b (Ne.symm hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (x : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ k, x k • gs b k⟫_ℝ = x j * ‖gs b j‖ ^ 2 := by
  exact inner_gs_sum_smul_gs b x j
end ReciprocityTheory.ReducedBases.T2

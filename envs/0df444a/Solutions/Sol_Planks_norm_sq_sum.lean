-- Prove2me | solution 1 for Planks.norm_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:00:17.724453+00:00
-- url     : https://prove2.me/submissions/a152b22b-51f3-4253-ac1e-4982ab269b0f

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E]
namespace Planks
theorem _root_.solution (y : ι → E) (hy : Orthonormal ℝ y) (c : ι → ℝ) :
    ‖∑ i, c i • y i‖ ^ 2 = ∑ i, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp hy]
  simp [sq]
end Planks

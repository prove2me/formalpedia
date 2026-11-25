-- Prove2me | solution 1 for SNumbers.sum_norm_sq_row_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:12:41.426339+00:00
-- url     : https://prove2.me/submissions/d595b2d4-71f0-4b15-8b28-7a8efd58411c

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_SNumbers_sum_norm_sq_le_sq_of_signedSum_le
public import Theorems.Thm_SNumbers_sum_norm_apply_le_norm_l1
attribute [local simp] SNumbers.signedSum_empty

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]
namespace SNumbers
theorem _root_.solution (A : H →L[𝕜] lp (fun _ : ι => 𝕜) 1) {w : ι → H}
    (hw : ∀ (j : ι) (x : H), (inner 𝕜 (w j) x : 𝕜) = A x j) (J : Finset ι) :
    ∑ j ∈ J, ‖w j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  refine sum_norm_sq_le_sq_of_signedSum_le 𝕜 fun S _ => ?_
  set z := signedSum w S J with hz
  -- Expand `⟪z, z⟫` using the rows: the signs reappear on the coordinates of `A z`.
  have hinner : (inner 𝕜 z z : 𝕜)
      = ∑ j ∈ J, (if j ∈ S then (A z) j else -((A z) j)) := by
    rw [hz, signedSum, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S
    · rw [if_pos hj, if_pos hj, hw]
    · rw [if_neg hj, if_neg hj, inner_neg_left, hw]
  have hle : ‖z‖ ^ 2 ≤ ‖A‖ * ‖z‖ :=
    calc ‖z‖ ^ 2 = RCLike.re (inner 𝕜 z z : 𝕜) := (inner_self_eq_norm_sq z).symm
      _ ≤ ‖(inner 𝕜 z z : 𝕜)‖ := RCLike.re_le_norm _
      _ = ‖∑ j ∈ J, (if j ∈ S then (A z) j else -((A z) j))‖ := by rw [hinner]
      _ ≤ ∑ j ∈ J, ‖(A z) j‖ := by
          refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
          by_cases hj : j ∈ S <;> simp [hj]
      _ ≤ ‖A z‖ := sum_norm_apply_le_norm_l1 _ J
      _ ≤ ‖A‖ * ‖z‖ := A.le_opNorm z
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg A
  · nlinarith [hle, hpos]
end SNumbers

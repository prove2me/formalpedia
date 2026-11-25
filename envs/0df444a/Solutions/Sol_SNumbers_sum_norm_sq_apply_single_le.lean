-- Prove2me | solution 1 for SNumbers.sum_norm_sq_apply_single_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:12:43.480327+00:00
-- url     : https://prove2.me/submissions/f7214f70-2dc8-40b0-ab72-4ab9a0d3eb84

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_SNumbers_sum_norm_sq_le_sq_of_signedSum_le
public import Theorems.Thm_SNumbers_norm_signedSum_single_le_one
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
theorem _root_.solution (B : lp (fun _ : ι => 𝕜) ∞ →L[𝕜] H) (J : Finset ι) :
    ∑ j ∈ J, ‖B (lp.single ∞ j (1 : 𝕜))‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  refine sum_norm_sq_le_sq_of_signedSum_le 𝕜 fun S _ => ?_
  have hmap : signedSum (fun j => B (lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜))) S J
      = B (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J) := by
    rw [signedSum, signedSum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S <;> simp [hj]
  rw [hmap]
  calc ‖B (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J)‖
      ≤ ‖B‖ * ‖signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J‖ :=
        B.le_opNorm _
    _ ≤ ‖B‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_signedSum_single_le_one S J) (norm_nonneg B)
    _ = ‖B‖ := mul_one _
end SNumbers

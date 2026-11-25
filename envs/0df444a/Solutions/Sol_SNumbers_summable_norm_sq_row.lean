-- Prove2me | solution 1 for SNumbers.summable_norm_sq_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:02.160936+00:00
-- url     : https://prove2.me/submissions/963e8438-a0f0-4038-896e-2a5a4a9bad34

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_sum_norm_sq_row_le

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
namespace SNumbers
theorem _root_.solution (A : H →L[𝕜] lp (fun _ : ℕ => 𝕜) 1) {w : ℕ → H}
    (hw : ∀ (j : ℕ) (x : H), (inner 𝕜 (w j) x : 𝕜) = A x j) :
    Summable fun j => ‖w j‖ ^ 2 :=
  summable_of_sum_range_le (fun _ => by positivity) fun n =>
    sum_norm_sq_row_le A hw (Finset.range n)
end SNumbers

-- Prove2me | solution 1 for SNumbers.norm_signedSum_single_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:25.067987+00:00
-- url     : https://prove2.me/submissions/721603f3-8493-4e80-b4a2-dad4c833cb45

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_SNumbers_signedSum_single_coord
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
theorem _root_.solution (S J : Finset ι) :
    ‖signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J‖ ≤ 1 := by
  refine lp.norm_le_of_forall_le zero_le_one fun i => ?_
  rw [signedSum_single_coord]
  by_cases hiJ : i ∈ J <;> by_cases hiS : i ∈ S <;> simp [hiJ, hiS]
end SNumbers

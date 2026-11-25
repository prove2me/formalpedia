-- Prove2me | solution 1 for SNumbers.signedSum_single_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:15.881943+00:00
-- url     : https://prove2.me/submissions/f94caa47-484e-42db-86e1-a19d14b9ca9d

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
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
theorem _root_.solution (S J : Finset ι) (i : ι) :
    (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J) i
      = if i ∈ J then (if i ∈ S then (1 : 𝕜) else -1) else 0 := by
  have hterm : ∀ j : ι,
      ((if j ∈ S then lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)
          else -lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) : lp (fun _ : ι => 𝕜) ∞) i
        = if i = j then (if j ∈ S then (1 : 𝕜) else -1) else 0 := by
    intro j
    by_cases hj : j ∈ S <;>
      by_cases hij : i = j <;>
        simp [hj, hij, lp.single_apply]
  rw [signedSum, lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp
end SNumbers

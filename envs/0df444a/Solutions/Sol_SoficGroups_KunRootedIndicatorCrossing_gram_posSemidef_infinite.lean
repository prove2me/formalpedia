-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.gram_posSemidef_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/5bc79fd5-a805-4777-b219-8e95002d6e7a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {I H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : I → H) :
    (Matrix.gram ℂ v).PosSemidef := by
  refine ⟨Matrix.isHermitian_gram ℂ v, ?_⟩
  intro c
  calc
    (0 : ℂ) ≤
        ⟪c.sum (fun i z => z • v i),
          c.sum (fun i z => z • v i)⟫_ℂ :=
      RCLike.nonneg_iff.mpr ⟨inner_self_nonneg, inner_self_im _⟩
    _ = c.sum (fun i z =>
          c.sum (fun j w => star z * (Matrix.gram ℂ v) i j * w)) := by
      rw [Finsupp.sum_inner]
      apply Finsupp.sum_congr
      intro i hi
      rw [Finsupp.inner_sum]
      apply Finsupp.sum_congr
      intro j hj
      simp only [inner_smul_left, inner_smul_right,
        Matrix.gram_apply, RCLike.star_def]
      ring
end SoficGroups.KunRootedIndicatorCrossing

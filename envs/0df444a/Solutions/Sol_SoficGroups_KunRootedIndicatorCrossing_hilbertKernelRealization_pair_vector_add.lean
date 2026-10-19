-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.hilbertKernelRealization_pair_vector_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/529e1eae-a80a-4281-b07a-c5b58d641c30

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
    {G : Type u} (K : Matrix (G × G) (G × G) ℂ)
    (R : HilbertKernelRealization K)
    (hadd : ∀ g h j : G, ∀ q : G × G,
      K (g, h) q + K (h, j) q = K (g, j) q)
    (g h j : G) :
    R.vector (g, h) + R.vector (h, j) = R.vector (g, j) := by
  have horth (q : G × G) :
      ⟪R.vector (g, h) + R.vector (h, j) - R.vector (g, j),
        R.vector q⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_add_left,
      R.gram, R.gram, R.gram, hadd]
    exact sub_self _
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_right, inner_add_right,
    horth (g, h), horth (h, j), horth (g, j)]
  simp
end SoficGroups.KunRootedIndicatorCrossing

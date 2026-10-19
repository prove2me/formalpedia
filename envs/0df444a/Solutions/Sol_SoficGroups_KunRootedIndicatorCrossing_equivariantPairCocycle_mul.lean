-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.equivariantPairCocycle_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/383d8dba-f1d5-4c25-a16d-f6ca6292be85

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_hilbertKernelRealization_pair_vector_add

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    (R : EquivariantHilbertKernelRealization K)
    (hadd : ∀ g h j : G, ∀ q : G × G,
      K (g, h) q + K (h, j) q = K (g, j) q)
    (a g : G) :
    equivariantPairCocycle R (a * g) =
      equivariantPairCocycle R a +
        R.representation a (equivariantPairCocycle R g) := by
  unfold equivariantPairCocycle
  rw [R.equivariant]
  simp only [mul_one]
  rw [add_comm]
  exact (hilbertKernelRealization_pair_vector_add K R.realization
    hadd (a * g) a 1).symm
end SoficGroups.KunRootedIndicatorCrossing

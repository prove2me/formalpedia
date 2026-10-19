-- Prove2me | solution 1 for SoficGroups.MidrankPermutationEnergy.rankDropCount_eq_sum_rankDecreasingVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/cd23792f-b72c-4534-a0c2-c071a3b20cf5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.MidrankPermutationEnergy
namespace SoficGroups.MidrankPermutationEnergy
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (u : V → ℝ) (p : ι → Equiv.Perm V) (H r : ℝ) :
    SoficGroups.rankDropCount
      (fun e : ι × V => u e.2)
      (fun e : ι × V => u (p e.1 e.2)) H r =
        ∑ i : ι,
          ((rankDecreasingVertices Finset.univ
            (offsetFloorRank u H r) (p i)).card : ℝ) := by
  classical
  unfold SoficGroups.rankDropCount
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  unfold rankDecreasingVertices offsetFloorRank
  exact Finset.sum_boole
    (fun x : V =>
      ⌊(u (p i x) + r) / H⌋ < ⌊(u x + r) / H⌋)
    Finset.univ
end SoficGroups.MidrankPermutationEnergy

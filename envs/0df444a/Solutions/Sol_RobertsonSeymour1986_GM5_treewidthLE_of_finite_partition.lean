-- Prove2me | solution 1 for RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:16:52.431757+00:00
-- url     : https://prove2.me/submissions/4179ea50-6843-46b9-9b71-1bb0b7efd9c8

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_RobertsonSeymour1986_GM5_treewidthLE_of_finite_partition_decompositions

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ)
    (ι : Type) [Fintype ι] (C : ι → Finset V)
    (hcover : ∀ v : V, ∃ i, v ∈ C i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hedge : ∀ x y : V, G.Adj x y → ∃ i, x ∈ C i ∧ y ∈ C i)
    (hwidth : ∀ i, RobertsonSeymour1986.GM5.TreewidthLE
      (G.induce {u : V | u ∈ C i}) w) :
    RobertsonSeymour1986.GM5.TreewidthLE G w := by
  apply RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition_decompositions
    G w ι C hcover hdisjoint hedge
  intro i
  exact hwidth i

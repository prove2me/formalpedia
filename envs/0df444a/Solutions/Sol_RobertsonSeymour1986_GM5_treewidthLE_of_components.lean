-- Prove2me | solution 1 for RobertsonSeymour1986.GM5.treewidthLE_of_components
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:11:11.266463+00:00
-- url     : https://prove2.me/submissions/8cc08a82-28e4-4009-aae2-175cf8d57824

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_RobertsonSeymour1986_GM5_treewidthLE_of_finite_partition
import Theorems.Thm_RobertsonSeymour1986_GM5_components_form_finite_partition

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ)
    (hcomp : ∀ v : V,
      RobertsonSeymour1986.GM5.TreewidthLE
        (G.induce {u : V | G.Reachable u v}) w) :
    RobertsonSeymour1986.GM5.TreewidthLE G w := by
  obtain ⟨ι, inst, C, hcover, hdisjoint, hedge, hwidth⟩ :=
    RobertsonSeymour1986.GM5.components_form_finite_partition G w hcomp
  letI : Fintype ι := inst
  exact RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition
    G w ι C hcover hdisjoint hedge hwidth
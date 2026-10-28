-- Prove2me | solution 1 for WilliamsonShmoys.retained_component_treewidth_of_bfs_bands
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:19:02.825998+00:00
-- url     : https://prove2.me/submissions/d5a49432-0d67-4725-9e3b-8eb25cf8ffd7

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_retained_component_bfs_band
import Theorems.Thm_WilliamsonShmoys_retained_component_treewidth_from_band

set_option autoImplicit false

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (hk : 0 < k) (hj : j < k)
    (hBands : ∀ (root : Fin n) (lo hi : Nat), hi - lo < k →
      RobertsonSeymour1986.GM5.TreewidthLE
        (G.induce {x : Fin n | G.Reachable root x ∧ lo ≤ G.dist root x ∧ G.dist root x ≤ hi}) (3 * k)) :
    ∀ v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j},
      RobertsonSeymour1986.GM5.TreewidthLE
        (((G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).induce
          {u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j} |
            (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v})) (3 * k) := by
  intro v
  obtain ⟨lo, hi, hspan, hcontain⟩ :=
    WilliamsonShmoys.retained_component_bfs_band G k j hk hj v
  have hband := hBands (WilliamsonShmoys.bakerRoot G v.1) lo hi hspan
  exact WilliamsonShmoys.retained_component_treewidth_from_band
    G k j v lo hi hspan hcontain hband
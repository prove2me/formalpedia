-- Prove2me | solution 1 for WilliamsonShmoys.planar_baker_band_treewidth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:11:36.549386+00:00
-- url     : https://prove2.me/submissions/4984bed3-44e5-4292-b006-56173259ff26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_planar_bfs_annulus_treewidth
import Theorems.Thm_WilliamsonShmoys_retained_component_treewidth_of_bfs_bands

set_option autoImplicit false

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat)
    (hk : 0 < k) (hj : j < k)
    (hG : WilliamsonShmoys.HasPlanarDrawing G) :
    ∀ v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j},
      RobertsonSeymour1986.GM5.TreewidthLE
        (((G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).induce
          {u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j} |
            (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v}))
        (3 * k) := by
  exact WilliamsonShmoys.retained_component_treewidth_of_bfs_bands
    G k j hk hj (by
      intro root lo hi hwidth
      exact WilliamsonShmoys.planar_bfs_annulus_treewidth G root k lo hi hwidth hG)
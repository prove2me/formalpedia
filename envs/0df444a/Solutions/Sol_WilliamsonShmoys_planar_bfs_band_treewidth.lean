-- Prove2me | solution 1 for WilliamsonShmoys.planar_bfs_band_treewidth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:03:07.49865+00:00
-- url     : https://prove2.me/submissions/23b6b0b3-d656-40a1-a882-139722ec8748
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_planar_baker_band_treewidth
import Theorems.Thm_RobertsonSeymour1986_GM5_treewidthLE_of_components

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat)
    (hk : 0 < k) (hj : j < k) (hG : HasPlanarDrawing G) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (G.induce {v : Fin n | bakerLevel G v % k ≠ j}) (3 * k) := by
  classical
  let H : SimpleGraph {v : Fin n // bakerLevel G v % k ≠ j} :=
    G.induce {v : Fin n | bakerLevel G v % k ≠ j}
  have hcomponents :
      ∀ v : {x : Fin n // bakerLevel G x % k ≠ j},
        RobertsonSeymour1986.GM5.TreewidthLE
          (H.induce {u : {x : Fin n // bakerLevel G x % k ≠ j} | H.Reachable u v})
          (3 * k) := by
    intro v
    exact WilliamsonShmoys.planar_baker_band_treewidth G k j hk hj hG v
  simpa [H] using
    RobertsonSeymour1986.GM5.treewidthLE_of_components H (3 * k) hcomponents
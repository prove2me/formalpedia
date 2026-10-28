-- Prove2me | solution 1 for WilliamsonShmoys.retained_component_treewidth_from_band
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:30:53.725103+00:00
-- url     : https://prove2.me/submissions/b77fd0b0-f80f-46fe-b9ed-284b991ebb43

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_retained_component_treewidth_from_band_induced_mono

set_option autoImplicit false

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat)
    (v : {x : Fin n // Not (WilliamsonShmoys.bakerLevel G x % k = j)})
    (lo hi : Nat)
    (hspan : hi - lo < k)
    (hcontain :
      forall u : {x : Fin n // Not (WilliamsonShmoys.bakerLevel G x % k = j)},
        (G.induce {x : Fin n | Not (WilliamsonShmoys.bakerLevel G x % k = j)}).Reachable u v ->
          G.Reachable (WilliamsonShmoys.bakerRoot G v.1) u.1 /\
            lo <= G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 /\
            G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 <= hi)
    (hband :
      RobertsonSeymour1986.GM5.TreewidthLE
        (G.induce
          {x : Fin n |
            G.Reachable (WilliamsonShmoys.bakerRoot G v.1) x /\
              lo <= G.dist (WilliamsonShmoys.bakerRoot G v.1) x /\
              G.dist (WilliamsonShmoys.bakerRoot G v.1) x <= hi})
        (3 * k)) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (((G.induce
          {x : Fin n | Not (WilliamsonShmoys.bakerLevel G x % k = j)}).induce
          {u : {x : Fin n // Not (WilliamsonShmoys.bakerLevel G x % k = j)} |
            (G.induce
                {x : Fin n | Not (WilliamsonShmoys.bakerLevel G x % k = j)}).Reachable
              u v}))
      (3 * k) := by
  exact WilliamsonShmoys.retained_component_treewidth_from_band_induced_mono
    G
    {x : Fin n | Not (WilliamsonShmoys.bakerLevel G x % k = j)}
    {x : Fin n |
      G.Reachable (WilliamsonShmoys.bakerRoot G v.1) x /\
        lo <= G.dist (WilliamsonShmoys.bakerRoot G v.1) x /\
        G.dist (WilliamsonShmoys.bakerRoot G v.1) x <= hi}
    (fun u =>
      (G.induce
          {x : Fin n | Not (WilliamsonShmoys.bakerLevel G x % k = j)}).Reachable
        u v)
    (by
      intro u hu
      exact hcontain u hu)
    (3 * k)
    hband
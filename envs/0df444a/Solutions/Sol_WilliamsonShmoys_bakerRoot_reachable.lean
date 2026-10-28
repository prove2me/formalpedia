-- Prove2me | solution 1 for WilliamsonShmoys.bakerRoot_reachable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:29:25.943147+00:00
-- url     : https://prove2.me/submissions/3b51d104-7a9c-4683-9652-c62bd7cf6ea6

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : G.Reachable (WilliamsonShmoys.bakerRoot G v) v := by
  classical
  unfold WilliamsonShmoys.bakerRoot
  have h := Finset.min'_mem (Finset.univ.filter (fun u => G.Reachable u v))
    ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl v⟩⟩
  convert (Finset.mem_filter.1 h).2

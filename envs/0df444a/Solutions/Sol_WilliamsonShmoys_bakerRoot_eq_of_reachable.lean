-- Prove2me | solution 1 for WilliamsonShmoys.bakerRoot_eq_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:29:26.014987+00:00
-- url     : https://prove2.me/submissions/65a4801b-9852-4140-9220-13e397a3036f

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) {u v : Fin n} (h : G.Reachable u v) : WilliamsonShmoys.bakerRoot G u = WilliamsonShmoys.bakerRoot G v := by
  classical
  unfold WilliamsonShmoys.bakerRoot
  have hs : (Finset.univ.filter (fun w => G.Reachable w u)) =
      (Finset.univ.filter (fun w => G.Reachable w v)) := by
    ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hw => hw.trans h, fun hw => hw.trans h.symm⟩
  congr 1

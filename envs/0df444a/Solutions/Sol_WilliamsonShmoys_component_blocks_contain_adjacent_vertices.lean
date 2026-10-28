-- Prove2me | solution 1 for WilliamsonShmoys.component_blocks_contain_adjacent_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:15:19.450764+00:00
-- url     : https://prove2.me/submissions/1d58a906-c747-4ace-8e22-a5cef78f0339

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ u v, G.Adj u v →
      ∃ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
        u ∈ C ∧ v ∈ C := by
  intro u v huv
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ u), by simp, by simpa using huv.reachable⟩

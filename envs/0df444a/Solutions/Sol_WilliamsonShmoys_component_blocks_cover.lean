-- Prove2me | solution 1 for WilliamsonShmoys.component_blocks_cover
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:15:10.610422+00:00
-- url     : https://prove2.me/submissions/32a6853f-cc3f-456d-90a8-64df769915e8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    (Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w))).biUnion id = Finset.univ := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, id, iff_true]
  exact ⟨_, ⟨v, rfl⟩, by simp⟩

-- Prove2me | solution 1 for WilliamsonShmoys.component_blocks_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:15:02.702999+00:00
-- url     : https://prove2.me/submissions/415e2cbf-efe6-4d36-b26e-c89467d0c215

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)), C.Nonempty := by
  intro C hC
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hC
  obtain ⟨v, rfl⟩ := hC
  exact ⟨v, by simp⟩

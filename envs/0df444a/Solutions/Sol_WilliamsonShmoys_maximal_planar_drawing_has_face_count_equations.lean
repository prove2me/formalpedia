-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_face_count_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:14:52.173988+00:00
-- url     : https://prove2.me/submissions/4ebdd9b9-2d5e-4443-af7d-228b17928d7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_edge_count
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    ∃ f : ℕ,
      L.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f = 2 * L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMplanar, hMedges⟩ :=
    WilliamsonShmoys.planar_graph_augmentation_edge_count L hV hLplanar
  have hML : M = L := hmax M hLM hMplanar
  subst M
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
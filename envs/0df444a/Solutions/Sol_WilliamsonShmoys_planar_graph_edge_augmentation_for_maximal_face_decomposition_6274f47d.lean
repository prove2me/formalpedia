-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_augmentation_for_maximal_face_decomposition_6274f47d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:15:11.069341+00:00
-- url     : https://prove2.me/submissions/532cd0ec-b08c-45fa-8093-fa0918c93fce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_6274f47d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_6274f47d

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSmall : L.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊂ M.edgeSet ∧ HasPlanarDrawingOn M := by
  obtain ⟨M, hLM, hPlanar, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_6274f47d L hL
  have hCount : M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_6274f47d M hPlanar hCard hMax
  refine ⟨M, ?_, hPlanar⟩
  refine ⟨hLM, ?_⟩
  intro hML
  have hEq : L.edgeSet = M.edgeSet := hMax L hML hL
  rw [hEq] at hSmall
  rw [hCount] at hSmall
  omega

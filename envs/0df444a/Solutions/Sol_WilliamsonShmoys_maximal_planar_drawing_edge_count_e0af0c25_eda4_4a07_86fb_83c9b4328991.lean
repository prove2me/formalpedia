-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_e0af0c25_eda4_4a07_86fb_83c9b4328991
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:54:53.638842+00:00
-- url     : https://prove2.me/submissions/270bcf0f-1aa0-4aca-b8e7-e958e2d283fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hNmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
      N hNdraw hCard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
      N hNdraw hNmax hCard
  omega
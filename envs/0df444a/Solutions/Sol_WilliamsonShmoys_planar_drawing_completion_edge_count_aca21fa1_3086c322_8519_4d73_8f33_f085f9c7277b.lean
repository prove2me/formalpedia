-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:21:29.590992+00:00
-- url     : https://prove2.me/submissions/21aafa2a-cd80-4594-a1f9-6c869516c677
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : HasPlanarDrawingOn Z)
    (hCard : 3 <= Fintype.card V) :
    ∃ W : SimpleGraph V,
      HasPlanarDrawingOn W ∧
      (∀ u v, Z.Adj u v → W.Adj u v) ∧
      (W.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨W, hW, hZW, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b Z hZ
  exact ⟨W, hW, hZW,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b W hW hMax hCard⟩
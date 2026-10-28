-- Prove2me | solution 1 for WilliamsonShmoys.planar_augment_below_triangulation_bound_36583a35
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:43:46.338974+00:00
-- url     : https://prove2.me/submissions/5f20c405-82f1-4a01-8e67-5c25f24c6a47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_has_maximal_drawable_supergraph_36583a35
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_36583a35

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : (K.edgeSet.ncard : Int) <
      3 * (Fintype.card V : Int) - 6) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ ¬ L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_has_maximal_drawable_supergraph_36583a35 K hK
  refine ⟨L, hKL, ?_, hPlanar⟩
  intro hLK
  have hCount :=
    WilliamsonShmoys.planar_maximal_edge_count_36583a35 L hPlanar hCard hMax
  have hEq : L = K := le_antisymm hLK hKL
  subst L
  omega
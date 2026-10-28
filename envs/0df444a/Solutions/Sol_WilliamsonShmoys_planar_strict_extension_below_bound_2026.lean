-- Prove2me | solution 1 for WilliamsonShmoys.planar_strict_extension_below_bound_2026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:58:43.381769+00:00
-- url     : https://prove2.me/submissions/b0dfffa9-58c0-4e10-a754-a4f2488e9283
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_for_strict_extension_below_bound_2026
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_for_strict_extension_below_bound_2026

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hFew : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, L ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ L := by
  obtain ⟨K, hLK, hK, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_for_strict_extension_below_bound_2026 L hL
  have hCount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_for_strict_extension_below_bound_2026
      K hK hCard hMax
  refine ⟨K, hLK, hK, ?_⟩
  intro hEq
  subst K
  omega
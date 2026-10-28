-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:09:38.6849+00:00
-- url     : https://prove2.me/submissions/4d07296e-afa3-4ada-bc4c-f07d1db7f010
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_b1db10ca_2200_4b55_8753_9bc7a07260c1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * (Fintype.card V : Int) - 6 = (L.edgeSet.ncard : Int) := by
  obtain ⟨M, hsub, hM, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_extension_b1db10ca_2200_4b55_8753_9bc7a07260c1
      L hV hL
  have hEq : M = L := hmax M hsub hM
  subst M
  exact hcount
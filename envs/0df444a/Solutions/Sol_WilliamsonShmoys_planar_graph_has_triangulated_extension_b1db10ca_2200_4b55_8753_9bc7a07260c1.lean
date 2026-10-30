-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_extension_b1db10ca_2200_4b55_8753_9bc7a07260c1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:34:36.334856+00:00
-- url     : https://prove2.me/submissions/e5aaa62b-aa51-4552-b8f6-c4161b14ec51

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_b9be61fe_8c1d_403c_9dc2_d4f84da24c92

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      And (LE.le L M)
        (And (WilliamsonShmoys.HasPlanarDrawingOn M)
          (3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int))) := by
  exact Exists.elim
    (WilliamsonShmoys.maximal_planar_supergraph_exists L hV hL)
    (fun M hm =>
      Exists.intro M
        (And.intro (And.left hm)
          (And.intro (And.left (And.right hm))
            (WilliamsonShmoys.maximal_planar_graph_edge_count_b9be61fe_8c1d_403c_9dc2_d4f84da24c92
              M hV (And.left (And.right hm)) (And.right (And.right hm))))))
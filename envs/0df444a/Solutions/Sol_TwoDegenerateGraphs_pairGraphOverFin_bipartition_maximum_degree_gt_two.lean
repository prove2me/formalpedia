-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_bipartition_maximum_degree_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/675faf8b-05eb-4e2b-9550-8c9f7f1f9e3e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_exists_adj_degree_gt_two
import Theorems.Thm_TwoDegenerateGraphs_bipartition_maximum_degree_gt_two_of_adj

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∀ coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2),
      ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin (Fintype.card (PairVertex baseSize depth)) =>
            coloring vertex = side)).sup
          (fun vertex => (pairGraphOverFin baseSize depth).degree vertex) := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraphOverFin_exists_adj_degree_gt_two baseSize depth hbase hdepth
  exact bipartition_maximum_degree_gt_two_of_adj
    (pairGraphOverFin baseSize depth) hadj hu hv
end TwoDegenerateGraphs

-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_exists_adj_degree_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/a09c7d77-5350-4ecf-a78e-240e8655a677

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_exists_adj_degree_gt_two

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : Fin (Fintype.card (PairVertex baseSize depth)),
      (pairGraphOverFin baseSize depth).Adj u v ∧
      2 < (pairGraphOverFin baseSize depth).degree u ∧
      2 < (pairGraphOverFin baseSize depth).degree v := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraph_exists_adj_degree_gt_two baseSize depth hbase hdepth
  let e := pairGraphOverFinIso baseSize depth
  refine ⟨e u, e v, (e.map_rel_iff).mpr hadj, ?_, ?_⟩
  · simpa only [e.degree_eq] using hu
  · simpa only [e.degree_eq] using hv
end TwoDegenerateGraphs

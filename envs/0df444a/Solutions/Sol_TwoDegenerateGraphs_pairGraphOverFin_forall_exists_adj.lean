-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_forall_exists_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/ef950524-4c32-4575-8207-eb62b70b19e4

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_connected
import Theorems.Thm_TwoDegenerateGraphs_baseSize_le_pairVertex_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize)
    (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
      ∃ neighbor,
        (pairGraphOverFin baseSize depth).Adj vertex neighbor := by
  have hcard : 2 ≤ Fintype.card (PairVertex baseSize depth) := by
    have hcard_base := baseSize_le_pairVertex_card baseSize depth
    omega
  letI : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) :=
    Fin.nontrivial_iff_two_le.mpr hcard
  intro vertex
  exact
    (pairGraphOverFin_connected baseSize depth (by omega) hdepth).preconnected
      |>.exists_adj_of_nontrivial vertex
end TwoDegenerateGraphs

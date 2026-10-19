-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/30979c91-2264-42c2-a453-7ec43848e230

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_connected

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairGraphOverFin baseSize depth).Connected :=
  (pairGraphOverFinIso baseSize depth).connected_iff.mp
    (pairGraph_connected baseSize depth hbase hdepth)
end TwoDegenerateGraphs

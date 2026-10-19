-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/d75887e7-87d7-448d-9ef0-528690fb275f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_isBipartite_of_iso
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_isBipartite

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ) :
    (pairGraphOverFin baseSize depth).IsBipartite :=
  isBipartite_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isBipartite baseSize depth)
end TwoDegenerateGraphs

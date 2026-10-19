-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_isTwoDegenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/0a72b7dc-45b5-4772-a9e9-4c1b7b338e02

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_isTwoDegenerate_of_iso
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_isTwoDegenerate

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ) :
    IsTwoDegenerate (pairGraphOverFin baseSize depth) :=
  isTwoDegenerate_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isTwoDegenerate baseSize depth)
end TwoDegenerateGraphs

-- Prove2me | solution 2 for TarchaBraids.pureBraid_le_halfTwist_closure_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:55:18.232323+00:00
-- url     : https://prove2.me/submissions/0faa8df3-6e51-44f4-8902-b1a4e1aaf41a

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_pureBraid_le_halfTwist_closure

open TarchaBraids BraidsLinksMCG

theorem solution (n : ℕ)
    (ih : (FundamentalGroup.map (configProj n) (baseOrdered n)).range ≤
      Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i))) :
    (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1))).range ≤
      Subgroup.closure
        (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) :=
  TarchaBraids.pureBraid_le_halfTwist_closure (n + 1)

-- Prove2me | solution 1 for SpilloverDuopoly.Switchers.eq_13_profit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:44:05.419904+00:00
-- url     : https://prove2.me/submissions/a58b2a23-8842-4532-a535-0f5e29157f9f

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model
open SpilloverDuopoly.Switchers

theorem solution(G : Params) (hS : G.Standing) (hcov : G.u0 ≤ G.CS G.pStar) :
    G.profitA G.pStar G.pStar = G.delta * G.piS ∧
    G.profitB G.pStar G.pStar = G.delta * G.piS := by
  simp only [Params.profitA, Params.profitB, Params.shareA, Params.shareB, lt_irrefl, and_false,
    if_false, eq_self_iff_true, and_true, hcov, if_true]
  unfold Params.pStar; constructor <;> ring

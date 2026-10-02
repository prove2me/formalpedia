-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.length_zero_determined
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:01:08.331982+00:00
-- url     : https://prove2.me/submissions/edd95dd1-b418-434b-98af-052c81e78af5

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree in
theorem solution (w : ℝ) :
    v1 (leaf w) = w ∧ v2 (leaf w) = w := by
  constructor
  · unfold v1
    simp only [payoff, Finset.inf'_const, Finset.sup'_const]
  · unfold v2
    simp only [payoff, Finset.inf'_const, Finset.sup'_const]

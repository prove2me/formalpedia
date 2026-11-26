-- Prove2me | solution 1 for TunnellChallenge.registeredResidualMatching_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:16:26.909833+00:00
-- url     : https://prove2.me/submissions/667d2126-4a85-49f1-8202-0e2fffdb5600

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_registeredResidualMatching_stable
import Theorems.Thm_TunnellMap_GloballyRanked_stable_unique


set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (N : CanonicalB n ≃ CanonicalA n) (hN : StableResidualMatching N) :
    N = registeredResidualMatching hodd hpos hbalance := by
  classical
  letI : Fintype (CanonicalB n) :=
    Fintype.ofEquiv _ (canonicalBOrbitEquiv n).symm
  letI : Fintype (CanonicalA n) :=
    Fintype.ofEquiv _ (canonicalAOrbitEquiv hpos).symm
  change (registeredResidualRanking hpos).Stable N at hN
  have hM := registeredResidualMatching_stable hodd hpos hbalance
  change (registeredResidualRanking hpos).Stable
    (registeredResidualMatching hodd hpos hbalance) at hM
  exact TunnellMap.GloballyRanked.stable_unique
    (registeredResidualRanking hpos) N
      (registeredResidualMatching hodd hpos hbalance) hN hM
end TunnellChallenge

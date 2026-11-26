-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_quarterTurn_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:42:54.371822+00:00
-- url     : https://prove2.me/submissions/4a82a7dd-c4a6-4918-8494-bce61d724588

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_tunnellMap_val
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_quarterTurn_one


set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (4 * ((p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) - p.1.2.1,
        p.1.1 - 2 * p.1.2.2,
        (p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_quarterTurn_one hodd hpos
    hsq (balance_transport hbalance) (bEquiv n p) hz h₁]
  rfl
end TunnellChallenge

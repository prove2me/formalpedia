-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:01:50.990377+00:00
-- url     : https://prove2.me/submissions/204daa8a-a219-4a49-a2bf-43854fbbe8b3

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution

set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    aEquiv n (tunnellMap hodd hpos hsq hbalance p) =
      TunnellMap.paperTunnellMapTotal hodd hpos hsq (balance_transport hbalance)
        (bEquiv n p) := by
  rw [tunnellMap, Equiv.apply_symm_apply]
end TunnellChallenge

-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:59:37.754572+00:00
-- url     : https://prove2.me/submissions/0cca5561-84c8-46e4-9f90-f43e71967b2a

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
    (tunnellMap hodd hpos hsq hbalance p).1 =
      ((TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.x,
        (TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.y,
        (TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.z) := rfl
end TunnellChallenge

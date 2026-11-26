-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:42:35.726933+00:00
-- url     : https://prove2.me/submissions/8e96817a-ee0f-4eca-ad14-9c6d99b7eec7

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_tunnellMap_val
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_even


set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.2.2 % 2 = 0) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1, p.1.2.1, p.1.2.2 / 2) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_even hodd hpos hsq
    (balance_transport hbalance) (bEquiv n p) hz]
  rfl
end TunnellChallenge

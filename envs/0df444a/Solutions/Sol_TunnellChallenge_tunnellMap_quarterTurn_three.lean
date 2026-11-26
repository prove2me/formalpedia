-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_quarterTurn_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:43:05.313267+00:00
-- url     : https://prove2.me/submissions/efdead75-707d-4b3d-ae7e-1964d5e04bbf

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_tunnellMap_val
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_quarterTurn_three


set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : (4 : ℤ) ∣ p.1.1) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (2 * p.1.2.2, p.1.2.1, -(p.1.1 / 4)) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_quarterTurn_three hodd hpos
    hsq (balance_transport hbalance) (bEquiv n p) hz h₁ h₂ h₃]
  rfl
end TunnellChallenge

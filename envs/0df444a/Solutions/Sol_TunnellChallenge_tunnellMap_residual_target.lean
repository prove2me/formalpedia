-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_residual_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:43:14.1818+00:00
-- url     : https://prove2.me/submissions/4f99c780-82ab-4030-91be-66645930b7f4

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_tunnellMap_apply
import Theorems.Thm_TunnellMap_directTargetUsed_iff
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_residual_target


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
    (h₃ : ¬ (4 : ℤ) ∣ p.1.1) :
    ¬ DirectTargetUsed (tunnellMap hodd hpos hsq hbalance p) := by
  rw [directTargetUsed_iff, tunnellMap_apply]
  exact TunnellMap.paperTunnellMapTotal_residual_target hodd hpos hsq
    (balance_transport hbalance) (bEquiv n p) hz
    (fun hc => by
      rcases hc with hc | hc | hc
      · exact h₁ hc
      · exact h₂ hc
      · exact h₃ hc)
end TunnellChallenge

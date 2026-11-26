-- Prove2me | solution 1 for TunnellChallenge.tunnellResidualMap_agrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:43:22.01279+00:00
-- url     : https://prove2.me/submissions/054ddca3-f553-4bf9-a1a9-2dd793aa41b5

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_tunnellMap_residual_value
import Theorems.Thm_TunnellMap_RecordDA_residualMapExecTotal_eq_canonical


set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    (tunnellResidualMap hodd hpos hsq hbalance s).1 =
      tunnellMap hodd hpos hsq hbalance s.1.1 := by
  apply (aEquiv n).injective
  rw [tunnellMap_residual_value]
  change (arEquiv n (tunnellResidualMap hodd hpos hsq hbalance s)).1 = _
  rw [tunnellResidualMap, Equiv.apply_symm_apply,
    TunnellMap.RecordDA.residualMapExecTotal_eq_canonical]
end TunnellChallenge

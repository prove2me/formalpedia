-- Prove2me | solution 1 for TunnellChallenge.tunnellMap_residual_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:04:05.506844+00:00
-- url     : https://prove2.me/submissions/b3bc873c-829e-499e-84b8-f5b8910a56e4

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
import Theorems.Thm_TunnellChallenge_tunnellMap_apply
import Theorems.Thm_TunnellMap_some_paperTunnellMapTotal


set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (x : BResidual n) :
    aEquiv n (tunnellMap hodd hpos hsq hbalance x.1.1) =
      (TunnellMap.canonicalResidualMapOf hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)) (brEquiv n x)).1 := by
  let p : TunnellMap.BRep n := bEquiv n x.1.1
  let q : TunnellMap.BOddRep n := boEquiv n x.1
  let y : TunnellMap.BResidual n := brEquiv n x
  have hz : ¬ p.1.z % 2 = 0 := by
    change ¬ x.1.1.1.2.2 % 2 = 0
    have hoddz : x.1.1.1.2.2 % 2 = 1 := Int.odd_iff.mp x.1.2
    omega
  have hd : ¬ TunnellMap.SourceUsedTriple p.1 := by
    intro hc
    apply x.2
    exact (directSourceUsed_iff x.1).mpr hc
  have hdq : ¬ TunnellMap.SourceUsedTriple q.1 := hd
  have hres := TunnellMap.RecordDA.residualMapExecOpt_eq_some hodd hpos hsq
    (coreResidualOrbitCardEq hodd hpos hbalance) y
  have hopt : TunnellMap.paperTunnellMapExecOpt hpos hsq p =
      some (TunnellMap.canonicalResidualMapOf hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)) y).1 := by
    rw [TunnellMap.paperTunnellMapExecOpt, dif_neg hz]
    change TunnellMap.oddMapExecOpt hpos hsq q = _
    calc
      TunnellMap.oddMapExecOpt hpos hsq q = Option.map Subtype.val
          (TunnellMap.RecordDA.residualMapExecOpt hpos hsq y) := dif_neg hdq
      _ = _ := congrArg (Option.map Subtype.val) hres
  rw [tunnellMap_apply]
  exact Option.some.inj
    ((TunnellMap.some_paperTunnellMapTotal hodd hpos hsq
      (balance_transport hbalance) p).trans hopt)
end TunnellChallenge

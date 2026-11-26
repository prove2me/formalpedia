-- Prove2me | solution 1 for TunnellChallenge.registeredResidualMatching_target_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:59:49.828723+00:00
-- url     : https://prove2.me/submissions/3ea8eb57-0d91-4f95-86f9-0a9b6f4816cf

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution

set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : CanonicalB n) :
    arEquiv n (registeredResidualMatching hodd hpos hbalance s).1 =
      TunnellMap.canonicalAResidualRepresentative hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)
            ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1))) := by
  change (arEquiv n) ((arEquiv n).symm _) = _
  exact (arEquiv n).apply_symm_apply _
end TunnellChallenge

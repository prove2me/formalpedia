-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerun_rerun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:09.744822+00:00
-- url     : https://prove2.me/submissions/75f4d6fd-2572-4e10-a8bc-da1395e2d143

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      ((terminalRun frames).held
          (canonicalTargetLift (residualTargetLift y))).elim fallback
        fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1 :=
  rfl
end TunnellMap.RecordDA

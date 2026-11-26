-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerun_of_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:29:59.954294+00:00
-- url     : https://prove2.me/submissions/f6366855-0680-4006-828c-a99b3840cc36

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_run_eq_of_reaches

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]
omit [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) {E : DARun n}
    (hreach : Reaches frames (DARun.initial (sourceRoster n)) E)
    (hstop : step frames E = none) :
    inverseByRerun frames fallback y =
      (E.held (canonicalTargetLift (residualTargetLift y))).elim fallback
        fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1 := by
  rw [inverseByRerun, run_eq_of_reaches frames hreach hstop]
end TunnellMap.RecordDA

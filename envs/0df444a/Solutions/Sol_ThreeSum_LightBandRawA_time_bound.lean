-- Prove2me | solution 1 for ThreeSum.LightBandRawA.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:36:24.941695+00:00
-- url     : https://prove2.me/submissions/09ce261b-6b8c-4263-82e3-1b99cde805dc

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_LightBandRawA

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}
namespace ThreeSum.LightBandRawA
theorem _root_.solution (N g : ℕ) : time N g ≤ 1000*(N+1)*(g+1) := by
  unfold time LightBandRawAStep.time LightBandRawARow.time copyTime fillTime
  nlinarith
end ThreeSum.LightBandRawA

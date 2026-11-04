-- Prove2me | solution 1 for ThreeSum.LightSourceResidues.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:03.23034+00:00
-- url     : https://prove2.me/submissions/0dddbf36-ff9f-439b-aca5-3183dec64b95

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceResidues
theorem _root_.solution (n p U D : ℕ) :
    time n p U D ≤
      254*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+6 := by
  unfold time LightResidues.residueBudget
  nlinarith
end ThreeSum.LightSourceResidues

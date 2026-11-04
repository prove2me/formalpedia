-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.setup_time_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:49.907026+00:00
-- url     : https://prove2.me/submissions/eeb580a9-f75c-44cf-a1de-19e2f43c1c4f

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_WeightedCache3SUM_Alias_edb473b3a50facd6
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {h B : ℕ} (H : Bounds h B) :
    LightLocalCoverSetup.time h ≤ 11000*B^5 := by
  have hbuild := LightLocalCoverCost.build_time_bound H.positive H.width H.vertices H.prime H.candidates H.rounds
  have hp2 : cols h ≤ B^2 := by
    have hp := Nat.pow_le_pow_left H.prime 2
    unfold cols
    nlinarith
  have hlog := Nat.log_le_self 2 (cols h)
  have hB : 1 ≤ B := H.positive
  have hL := H.width
  have hpow15 := Nat.le_self_pow (by decide : 5 ≠ 0) B
  have hpow25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hB5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverSetup.time LightNatPower.time log2Time
  omega
end ThreeSum.LightLocalCoverResources

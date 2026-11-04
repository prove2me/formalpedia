-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.solvedInTime_of_claim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:17.750019+00:00
-- url     : https://prove2.me/submissions/6c9f9a6d-603a-4f30-8388-6aa5f3620164

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_WeightedCache3SUM_Alias_b08943e3ece6cc44

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperBigOPow a) :
    SolvedInTime Q a 0 := by
  intro κ
  obtain ⟨T, hT, C, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact solvedAt_of_realized T κ (hR T hT) (C := C)
    (by simpa only [pow_zero, mul_one] using hb)
end ThreeSumApsp.FromClaims

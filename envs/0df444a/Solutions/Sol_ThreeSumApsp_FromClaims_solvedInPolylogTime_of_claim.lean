-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.solvedInPolylogTime_of_claim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:55.63548+00:00
-- url     : https://prove2.me/submissions/f2fea59b-8c20-4d67-aa83-dff597c0d60f

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
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by
  intro κ
  obtain ⟨T, hT, C, e, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact ⟨e, solvedAt_of_realized T κ (hR T hT) hb⟩
end ThreeSumApsp.FromClaims

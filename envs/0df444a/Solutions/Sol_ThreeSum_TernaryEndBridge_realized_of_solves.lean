-- Prove2me | solution 1 for ThreeSum.TernaryEndBridge.realized_of_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:02:14.806984+00:00
-- url     : https://prove2.me/submissions/0e50e9b5-a5ad-4aa0-85e7-792dc3de45c0

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Theorems.Thm_Light_IsHost_solvedIn
import Definitions.Def_WeightedCache3SUM_Alias_8e84616b1c5210c7
import Theorems.Thm_Light_Solves_solvedIn


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section
namespace ThreeSum.TernaryEndBridge
theorem _root_.solution {P : Program} {p : ℕ}
    {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum (timeUpTo T) :=
  Light.Sec3.realized_threeSum _ (hs.solvedIn hp)
end ThreeSum.TernaryEndBridge

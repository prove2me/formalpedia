-- Prove2me | solution 1 for ThreeSum.TernaryHybridResources.fast_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:05.145353+00:00
-- url     : https://prove2.me/submissions/58f79358-26a0-4b1e-ae3a-b3fb3828c638

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Theorems.Thm_ThreeSum_TernaryHybridResources_fast_at_depth_of_ok

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)
namespace ThreeSum.TernaryHybridResources
theorem _root_.solution {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    (fastNeed n (n^κ)).Ok lim free (d+1) :=
  fast_at_depth_of_ok fastNeed H (by omega)
end ThreeSum.TernaryHybridResources

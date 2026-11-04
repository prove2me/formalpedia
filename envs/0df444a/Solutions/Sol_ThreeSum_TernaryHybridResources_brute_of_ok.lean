-- Prove2me | solution 1 for ThreeSum.TernaryHybridResources.brute_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:06.310515+00:00
-- url     : https://prove2.me/submissions/b01ab4ba-5e01-417c-b20d-abcdb9b76d1f

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Theorems.Thm_ThreeSum_TernaryHybridResources_brute_at_depth_of_ok

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)
namespace ThreeSum.TernaryHybridResources
theorem _root_.solution {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    (LightBruteThreeSum.need n U).Ok lim free (d+1) :=
  brute_at_depth_of_ok fastNeed H (by omega)
end ThreeSum.TernaryHybridResources

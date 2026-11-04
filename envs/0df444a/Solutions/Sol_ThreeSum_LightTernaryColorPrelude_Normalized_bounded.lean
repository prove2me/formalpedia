-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.Normalized.bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:38:45.959984+00:00
-- url     : https://prove2.me/submissions/ff15febf-232c-40aa-9cf4-2da6192c2e6a

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryColorPrelude
namespace Normalized
theorem _root_.solution {μ : ℕ→ℤ} {base n U : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) (hb : ∀ z∈original, |z|≤(U:ℤ)) :
    ∀ z∈L, |z|≤(U:ℤ) :=fun z hz=>hb z ((H.mem z).mp hz)
end Normalized
end ThreeSum.LightTernaryColorPrelude

-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.Normalized.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:40:39.11303+00:00
-- url     : https://prove2.me/submissions/c130f102-eb0d-4e18-8c58-47433379ea0d

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryColorPrelude
namespace Normalized
theorem _root_.solution {μ ν : ℕ→ℤ} {base n cut : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) (hk : Kept μ ν cut) (hb : base+n≤cut) :
    Normalized ν base n original L :=
  {H with seg:=fun i hi=>(hk (base+i) (by have hh:=H.length; omega)).trans (H.seg i hi)}
end Normalized
end ThreeSum.LightTernaryColorPrelude

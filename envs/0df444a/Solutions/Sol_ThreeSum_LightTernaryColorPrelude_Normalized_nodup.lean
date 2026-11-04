-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.Normalized.nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:40:54.784076+00:00
-- url     : https://prove2.me/submissions/6a208527-e5fc-48f5-8b07-e8e9ac596e6e

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
theorem _root_.solution {μ : ℕ→ℤ} {base n : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) : L.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (H.sorted.imp (fun h=>ne_of_lt h))
end Normalized
end ThreeSum.LightTernaryColorPrelude

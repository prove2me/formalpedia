-- Prove2me | solution 1 for TDLC.Refutation.noBadStep2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:28:20.598822+00:00
-- url     : https://prove2.me/submissions/5ec44621-996a-4465-b371-60e1bfcdf4fb

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_noBadPath2

set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution : ¬ Nonempty (Step2 badLeft badRight) := by
  intro ⟨cell⟩
  exact noBadPath2 ⟨Path2.singleton cell⟩
end TDLC.Refutation

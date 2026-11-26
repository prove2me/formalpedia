-- Prove2me | solution 1 for TDLC.Refutation.notNatPath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:28:21.058278+00:00
-- url     : https://prove2.me/submissions/00425846-c037-4508-a03d-f54a7da63852

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_noBadPath2

set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution : ¬ Nonempty NatPath := by
  intro ⟨nat⟩
  exact noBadPath2 ⟨nat (f := fun x => x) (g := fun x => x)
    (fun x => Path.lEmbed (badFamily x)) testPath⟩
end TDLC.Refutation

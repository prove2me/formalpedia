-- Prove2me | solution 1 for TDLC.Refutation.notStepNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:28:44.654436+00:00
-- url     : https://prove2.me/submissions/ee25b4b9-97d2-4225-b7bd-4bdd7c1c924d

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_noBadStep2

set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution : ¬ Nonempty StepNat := by
  intro ⟨nat⟩
  exact noBadStep2 ⟨nat (f := fun x => x) (g := fun x => x) badFamily testStep⟩
end TDLC.Refutation

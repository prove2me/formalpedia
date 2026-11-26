-- Prove2me | solution 1 for TDLC.Refutation.noBadPath2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:56.367173+00:00
-- url     : https://prove2.me/submissions/167ab4c4-c93c-4f02-bccc-cf3e6588bf84

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_path2_preserves
import Theorems.Thm_TDLC_Refutation_badLeft_grade
import Theorems.Thm_TDLC_Refutation_badRight_grade

set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution : ¬ Nonempty (Path2 badLeft badRight) := by
  intro ⟨cells⟩
  have h := path2_preserves dihedral diagonalMarker cells valuation
  rw [badLeft_grade, badRight_grade] at h
  exact (by decide : (1 : Fin 6) ≠ 2) h
end TDLC.Refutation

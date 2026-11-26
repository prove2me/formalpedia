-- Prove2me | solution 1 for TDLC.Refutation.path2_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:28.964107+00:00
-- url     : https://prove2.me/submissions/67e7ef4c-b182-4288-85e5-9bdaa0240ea1

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_cell_preserves

set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by
  induction cells with
  | nil2 => rfl
  | seq2 c cs ih => exact (cell_preserves g mark c val).trans ih
end TDLC.Refutation

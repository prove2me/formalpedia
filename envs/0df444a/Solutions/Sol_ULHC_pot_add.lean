-- Prove2me | solution 1 for ULHC.pot_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:24.319678+00:00
-- url     : https://prove2.me/submissions/ffdd595f-5416-4942-b2a0-18144104e340

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential

set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution (E : Finset Edge) (w₁ w₂ : Edge → ℤ) (c : Pt) :
    pot E (fun e => w₁ e + w₂ e) c = pot E w₁ c + pot E w₂ c := by
  unfold pot; rw [Finset.sum_add_distrib]
end ULHC

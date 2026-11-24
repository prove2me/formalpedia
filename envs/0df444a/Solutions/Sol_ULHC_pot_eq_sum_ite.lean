-- Prove2me | solution 1 for ULHC.pot_eq_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:26.15171+00:00
-- url     : https://prove2.me/submissions/64442360-22b9-467c-93f8-fcc61400f647

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential

set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution (c : Pt) :
    pot E w c = ∑ e ∈ E, if RowSel c e then w e else 0 := by
  unfold pot; rw [Finset.sum_filter]
end ULHC

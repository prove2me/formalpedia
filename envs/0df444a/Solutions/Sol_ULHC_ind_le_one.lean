-- Prove2me | solution 1 for ULHC.ind_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:56.018874+00:00
-- url     : https://prove2.me/submissions/0e8bbd24-bd49-41fd-a4b1-34b9f94981cd

import Mathlib
import Definitions.Def_ULHC_Grid

set_option autoImplicit true
open ULHC
namespace ULHC
theorem _root_.solution (F : Finset Edge) (e : Edge) : ind F e ≤ 1 := by
  unfold ind; split <;> omega
end ULHC

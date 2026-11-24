-- Prove2me | solution 1 for ULHC.Mz_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:18:55.427395+00:00
-- url     : https://prove2.me/submissions/f299b478-f9cf-4242-87d3-23c3fc8d4c20

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution (G : Finset Edge) : ncomp V G * (2 * Dm V + 4) + 1 ≤ Mz V G := by
  unfold Mz
  split_ifs <;> omega
end ULHC

-- Prove2me | solution 1 for ULHC.extra_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:22:59.860845+00:00
-- url     : https://prove2.me/submissions/80125ddf-63ad-4b81-ba93-54eb4802f001

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_dval_le

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G : Finset Edge} (hGV : Inside V G) :
    Mz V G ≤ ncomp V G * (2 * Dm V + 4) + (2 * Dm V + 2) := by
  have hd := dval_le hGV
  unfold Mz
  split_ifs <;> omega
end ULHC

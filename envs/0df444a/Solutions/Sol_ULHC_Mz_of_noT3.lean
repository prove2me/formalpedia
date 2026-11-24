-- Prove2me | solution 1 for ULHC.Mz_of_noT3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:18:57.107453+00:00
-- url     : https://prove2.me/submissions/9e991a4f-99bb-403a-8b1e-799f9a953a8d

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G : Finset Edge} (hT : NoTypeIII V G) :
    Mz V G = ncomp V G * (2 * Dm V + 4) + (2 * dval V G + 2) := by
  unfold Mz
  rw [if_pos hT]
end ULHC

-- Prove2me | solution 1 for ULHC.Mz_of_T3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:19:01.748897+00:00
-- url     : https://prove2.me/submissions/1ab41199-fd5b-4cd3-8a19-3cd06b6ffa45

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G : Finset Edge} (hT : ¬ NoTypeIII V G) :
    Mz V G = ncomp V G * (2 * Dm V + 4) + 1 := by
  unfold Mz
  rw [if_neg hT]
end ULHC

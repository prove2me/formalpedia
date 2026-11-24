-- Prove2me | solution 1 for ULHC.cellJ_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:32.134515+00:00
-- url     : https://prove2.me/submissions/df59bdd9-062f-4882-94f3-34520a969754

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_nb_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (j : ℕ) : nb (cellJ c s (j + 1)) s.opp = cellJ c s j := by
  rw [← nb_cellJ, nb_nb_opp]
end ULHC

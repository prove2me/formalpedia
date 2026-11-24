-- Prove2me | solution 1 for ULHC.side2_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:13.19302+00:00
-- url     : https://prove2.me/submissions/e932ebaf-8b10-4763-8ea9-1a7533cb40bc

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_nb_comm_lat
import Theorems.Thm_ULHC_nb_nb_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (j : ℕ) :
    nb (nb (cellJ c s (j + 1)) (latB s)) s.opp = nb (cellJ c s j) (latB s) := by
  rw [← (nb_comm_lat c s j).2, nb_nb_opp]
end ULHC

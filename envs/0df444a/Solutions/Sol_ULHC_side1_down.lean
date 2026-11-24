-- Prove2me | solution 1 for ULHC.side1_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:04.627449+00:00
-- url     : https://prove2.me/submissions/de991b63-4d89-400e-9e1b-1670dc347a01

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_nb_comm_lat
import Theorems.Thm_ULHC_nb_nb_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (j : ℕ) :
    nb (nb (cellJ c s (j + 1)) (latA s)) s.opp = nb (cellJ c s j) (latA s) := by
  rw [← (nb_comm_lat c s j).1, nb_nb_opp]
end ULHC

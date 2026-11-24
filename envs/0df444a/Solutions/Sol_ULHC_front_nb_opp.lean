-- Prove2me | solution 1 for ULHC.front_nb_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:33:36.849128+00:00
-- url     : https://prove2.me/submissions/59a2808b-3fa6-4fe5-825d-d4cc549d2025

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_opp_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : front (nb c s.opp) s = back c s := by
  have := back_nb (nb c s.opp) s
  rw [show nb (nb c s.opp) s = c by
    have h := nb_nb_opp c s.opp; rwa [opp_opp] at h] at this
  exact this.symm
end ULHC

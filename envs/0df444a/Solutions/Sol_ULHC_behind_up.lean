-- Prove2me | solution 1 for ULHC.behind_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:21:17.222349+00:00
-- url     : https://prove2.me/submissions/5553387a-fea7-454b-ba79-31f09e364b64

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_opp_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : nb (nb c s.opp) s = c := by
  have h := nb_nb_opp c s.opp; rwa [opp_opp] at h
end ULHC

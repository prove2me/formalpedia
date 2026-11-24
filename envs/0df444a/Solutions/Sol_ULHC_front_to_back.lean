-- Prove2me | solution 1 for ULHC.front_to_back
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:34:17.439181+00:00
-- url     : https://prove2.me/submissions/ec1e0c8e-8494-4f51-8028-f459aec45bbf

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {A : Finset Edge} {d : Pt} {s : Side} (h1 : lat1 d s ∈ A) (h2 : lat2 d s ∈ A)
    (hn : ¬ Conn A (front1 d s) (front2 d s)) : ¬ Conn A (back1 d s) (back2 d s) := fun h =>
  hn ((((ends_lat1 d s).conn h1).symm.trans h).trans ((ends_lat2 d s).conn h2))
end ULHC

-- Prove2me | solution 1 for ULHC.pw_posList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:57:15.6088+00:00
-- url     : https://prove2.me/submissions/06d587a8-87df-43e9-9e6e-c4b7b671dd0e

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_MP_pw_cons


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution : ∀ (L : List StripSpec) (k : ℕ),
    MP.pw gw (posList k L) = (L.map StripSpec.n).sum
  | [], _ => rfl
  | σ :: L, k => by
    rw [posList, MP.pw_cons, solution L, List.map_cons, List.sum_cons]
    rfl
end ULHC

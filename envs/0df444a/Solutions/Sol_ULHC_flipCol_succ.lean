-- Prove2me | solution 1 for ULHC.flipCol_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:51.268796+00:00
-- url     : https://prove2.me/submissions/88e23b98-e2b7-4a42-8e4f-a209e944c261

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_APair_flip


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution (F : Finset Edge) (n : ℕ) :
    flipCol F c s (n + 1) = flipCol (flip F (cellJ c s n)) c s n := rfl
end ULHC

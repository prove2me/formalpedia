-- Prove2me | solution 1 for ULHC.mem_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:33.903356+00:00
-- url     : https://prove2.me/submissions/464748c6-7020-4844-846b-1ae743e9c3b1

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_mem_flipCol


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
omit hk hpat
namespace ULHC
theorem _root_.solution (e : Edge) :
    e ∈ flipCol F c s (k + 2) ↔ (e ∈ F ↔ nOn c s (k + 2) e % 2 = 0) := mem_flipCol F c s _ e
end ULHC

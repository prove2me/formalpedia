-- Prove2me | solution 1 for ULHC.suf_cellJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:33.828468+00:00
-- url     : https://prove2.me/submissions/19096941-fba0-42be-bd15-8ee1399b2e55

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_cellJ_add

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}
namespace ULHC
theorem _root_.solution (j : ℕ) : cellJ (suf z i).c (suf z i).s j = cellJ z.c z.s (i + j) :=
  cellJ_add z.c z.s i j
end ULHC

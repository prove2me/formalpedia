-- Prove2me | solution 1 for ULHC.notTypeIII_of_not_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:39:36.096911+00:00
-- url     : https://prove2.me/submissions/d5111128-310b-402b-a8a1-f25f21e9428c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_alt_of_pattern

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {d : Pt} (h : ¬ Alt F d) :
    NotTypeIII V F d := fun _ h1 h2 h3 h4 => absurd (alt_of_pattern h1 h2 h3 h4) h
end ULHC

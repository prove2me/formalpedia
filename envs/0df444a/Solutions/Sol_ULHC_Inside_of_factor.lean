-- Prove2me | solution 1 for ULHC.Inside.of_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:40.779547+00:00
-- url     : https://prove2.me/submissions/ca65f212-ea92-4ec6-be7a-ebdacbc8bcde

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Inside
theorem _root_.solution {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge} (h : IsFactor V d F) :
    Inside V F := fun e he => h.1 e he
end Inside
end ULHC

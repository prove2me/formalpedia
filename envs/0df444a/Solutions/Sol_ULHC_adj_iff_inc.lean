-- Prove2me | solution 1 for ULHC.adj_iff_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:19.618015+00:00
-- url     : https://prove2.me/submissions/dec5e8bc-9629-4d35-bc26-b5ae9b439232

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {x y : Pt} :
    Adj F x y ↔ ∃ e ∈ F, (e.p = x ∧ e.q = y) ∨ (e.p = y ∧ e.q = x) := Iff.rfl
end ULHC

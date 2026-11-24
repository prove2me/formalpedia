-- Prove2me | solution 1 for ULHC.GE_inside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:25:50.146992+00:00
-- url     : https://prove2.me/submissions/886c5808-3b55-4dd2-b6da-8ca486860ea1

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_mem_GE

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (V : Finset Pt) : ∀ e ∈ GE V, e.p ∈ V ∧ e.q ∈ V := fun _ he => mem_GE.1 he
end ULHC

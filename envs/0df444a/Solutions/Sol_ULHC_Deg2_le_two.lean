-- Prove2me | solution 1 for ULHC.Deg2.le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:19:13.318775+00:00
-- url     : https://prove2.me/submissions/d91485d9-642d-4b22-bb54-96af19554519

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_deg_zero_of_inside

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Deg2
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) (z : Pt) : deg F z ≤ 2 := by
  by_cases hz : z ∈ V
  · rw [h.2 z hz]
  · rw [deg_zero_of_inside h.1 hz]; omega
end Deg2
end ULHC

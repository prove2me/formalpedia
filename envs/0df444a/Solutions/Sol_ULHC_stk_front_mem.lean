-- Prove2me | solution 1 for ULHC.stk_front_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:03.268788+00:00
-- url     : https://prove2.me/submissions/fe765e47-256c-4efd-9b3b-8e61190162a6

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_mem_cellE_frame
import Theorems.Thm_ULHC_back_nb


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : front c s ∈ cellE (nb c s) := by
  rw [mem_cellE_frame (nb c s) s _, back_nb]; exact Or.inl rfl
end ULHC

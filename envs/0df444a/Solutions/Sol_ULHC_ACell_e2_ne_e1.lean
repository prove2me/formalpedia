-- Prove2me | solution 1 for ULHC.ACell.e2_ne_e1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:22.170161+00:00
-- url     : https://prove2.me/submissions/63eeea73-11b4-4289-88e1-0a4cbd8842e9

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset Classical
open ULHC.ACell
variable (C : ACell)
namespace ULHC.ACell
theorem _root_.solution : C.e2 ≠ C.e1 := by
  intro h
  have h2 := C.h2; rw [h] at h2
  have := (C.h1.inc_iff C.d).1 ((h2.inc_iff C.d).2 (Or.inl rfl))
  rcases this with h | h
  · exact C.ad h.symm
  · exact C.bd h.symm
end ULHC.ACell

-- Prove2me | solution 1 for ULHC.deg_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:46.331035+00:00
-- url     : https://prove2.me/submissions/faed19e3-b85f-46e3-adde-8cb0f589fd85

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_ind_erase
import Theorems.Thm_ULHC_inc_count

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) (y : Pt) :
    deg (F.erase e) y + (if e.p = y ∨ e.q = y then 1 else 0) = deg F y := by
  rw [← inc_count e y]
  unfold deg
  have h1 := ind_erase he (eR y)
  have h2 := ind_erase he (eU y)
  have h3 := ind_erase he (eL y)
  have h4 := ind_erase he (eD y)
  omega
end ULHC

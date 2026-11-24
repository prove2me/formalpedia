-- Prove2me | solution 1 for ULHC.par_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:18:38.340813+00:00
-- url     : https://prove2.me/submissions/47e05b30-124d-4de2-a8ad-aa0f70f0d234

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_par_add_fst
import Theorems.Thm_ULHC_par_add_snd
import Theorems.Thm_ULHC_par_sub_fst
import Theorems.Thm_ULHC_par_sub_snd


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : par (nb c s) = !par c := by
  obtain ⟨x, y⟩ := c
  cases s
  · exact par_sub_snd (x, y)
  · exact par_add_snd (x, y)
  · exact par_sub_fst (x, y)
  · exact par_add_fst (x, y)
end ULHC

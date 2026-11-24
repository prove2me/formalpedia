-- Prove2me | solution 1 for ULHC.TF.nbr_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:15.3538+00:00
-- url     : https://prove2.me/submissions/212cf74b-637f-4180-a382-64b375cfb6f1

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_inside_end
import Theorems.Thm_ULHC_TF_mem_nbr
import Theorems.Thm_ULHC_other_inc


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (u : Pt) : nbr V F u ⊆ V := by
  intro v hv
  obtain ⟨e, -, hf, rfl⟩ := mem_nbr.1 hv
  exact inside_end hf.1 other_inc
end ULHC.TF
